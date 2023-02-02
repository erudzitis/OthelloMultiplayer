package server.handlers;

import exceptions.HandshakeFailed;
import networking.Protocol;
import server.GameRoom;
import server.Server;

import java.io.*;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

/**
 * Class that acts as a middle-man between the Server and Client,
 * and provides reciprocal communication,
 * handles incoming protocol commands from the Client 'through' Server.
 */
public class ClientHandler implements Runnable {
    /*@public invariant clientSocket != null;
      @public invariant server != null;*/

    /**
     * Holds the socket of the assigned client.
     */
    private final /*@spec_public; @*/ Socket clientSocket;

    /**
     * Holds the output of the client socket.
     */
    private final PrintWriter clientSocketOutput;

    /**
     * Holds the reference back to the server.
     */
    private final /*@spec_public; @*/ Server server;

    /**
     * Indicates whether the initial handshake between the client and server has been established
     * Only having established a handshake,
     * can the client and server continue with any other communication.
     */
    private boolean handshakeAcknowledged = false;

    /**
     * Holds the list of all extensions the client supports.
     */
    private final List<String> clientSupportedExtensions = new ArrayList<>();

    /**
     * Constructor that initializes each client handler
     *
     * @param clientSocket Socket of the client
     * @throws IOException if IO communication establishment with the clients Socket
     *                     was not successful
     */
    /*@requires server != null;
      @requires clientSocket != null;
      @signals_only IOException; */
    public ClientHandler(Server server, Socket clientSocket) throws IOException {
        this.server = server;
        this.clientSocket = clientSocket;

        // Attempting to initialize wrappers for client IO
        // OutputStreamWriter converts the incoming chars to bytes,
        // buffered wrappers are for convenience / performance reasons
        this.clientSocketOutput = new PrintWriter(new OutputStreamWriter(
            clientSocket.getOutputStream()));
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        try (BufferedReader clientSocketInput = new BufferedReader(
            new InputStreamReader(clientSocket.getInputStream()))) {
            // Reading line by line
            String line;

            while ((line = clientSocketInput.readLine()) != null) {
                // Attempting to finalize handshake acknowledgment
                try {
                    this.acknowledgeHandshake(line);
                } catch (HandshakeFailed e) {
                    // We haven't performed the handshake yet,
                    // waiting for the client to send the initialization HELLO sequence,
                    // ignoring all other messages otherwise
                    continue;
                }

                // Handshake has been performed, we handle other valid 'commands'
                this.handleIncomingCommand(line);
            }

            // Connection lost, handle it appropriately
            this.terminateConnection();
        } catch (IOException e) {
            this.terminateConnection();
        }
    }

    /**
     * Internal method that sends acknowledgment HELLO protocol sequence to the client.
     */
    private void sendAcknowledgeHandshake() {
        // Sending the handshake acknowledgment to the client
        this.sendMessage(Protocol.helloFormat(Server.SERVER_DESCRIPTION,
            Server.SUPPORTED_EXTENSIONS));
    }

    /**
     * Internal method that
     * (assuming the message is actually a handshake initialization incoming from client),
     * acknowledges the handshake updates the clients supported extensions.
     *
     * @param line String protocol message read from input
     * @throws HandshakeFailed if the incoming message is not HELLO protocol adherent
     */
    /*@requires line != null;
      @assignable handshakeAcknowledged;
      @signals_only HandshakeFailed; */
    private void acknowledgeHandshake(String line) throws HandshakeFailed {
        // Handshake is already acknowledged
        if (this.handshakeAcknowledged) {
            return;
        }

        // Getting the supported extensions extracted from client protocol message
        List<String> supportedExtensions = Protocol.helloExtract(line);

        // Not a valid handshake message, ignoring!
        if (supportedExtensions == null) {
            throw new HandshakeFailed();
        }

        // Appending all extensions that client supports (if any)
        this.clientSupportedExtensions.addAll(supportedExtensions);

        // Sending back the handshake acknowledgment from the server,
        // providing all the extensions that the server supports
        this.sendAcknowledgeHandshake();

        // Updating state and waiting for next commands
        this.handshakeAcknowledged = true;
    }

    /**
     * Method that states if the current client that the client handler is assigned to
     * is logged into the server.
     *
     * @return true / false
     */
    public boolean isClientLoggedIn() {
        return this.server.getClientHandlers().get(this) != null;
    }

    /**
     * Internal method that attempts to terminate client connection.
     */
    private void terminateConnection() {
        try {
            this.clientSocket.close();
            this.server.clientDisconnected(this);
        } catch (IOException ignored) { }
    }

    /**
     * Internal method that handles all incoming commands from the client
     *
     * @param line String line that we received from the server
     */
    /*@requires line != null;
      @requires isClientLoggedIn(); @*/
    private void handleIncomingCommand(String line) {
        String command = Protocol.commandExtract(line);

        // Fall-through is not needed, using enhanced switch statement
        switch (command) {
            case Protocol.LOGIN -> this.handleLoginCommand(line);
            case Protocol.LIST -> {
                // Client must be logged in to perform this action
                if (!isClientLoggedIn()) {
                    break;
                }

                // Sends client the list of all logged-in user usernames
                this.sendMessage(Protocol.listFormat(this.server.getUserUsernames()));
            }
            case Protocol.QUEUE -> {
                // Client must be logged in to perform this action
                if (!isClientLoggedIn()) {
                    break;
                }

                // Client wants to join \ leave the queue (if already placed in the queue)
                // However, if client is already in a game, he should not be able to be put in queue
                this.server.setQueue(this);
            }
            case Protocol.MOVE -> {
                // Client must be logged in to perform this action
                if (!isClientLoggedIn()) {
                    break;
                }
                this.handleMoveCommand(line);
            }
            case Protocol.DISCONNECT -> this.terminateConnection();
        }
    }

    /**
     * Internal method that handles the login command issued by the client.
     *
     * @param line String protocol message
     */
    private void handleLoginCommand(String line) {
        // A user can log in if the provided username is not taken
        String clientDesiredUsername = Protocol.loginExtract(line);

        // Username is invalid, taken, or the username is too long,
        // client has to try to log in again
        if (clientDesiredUsername == null
                || this.server.isUsernameTaken(clientDesiredUsername)
                || clientDesiredUsername.length() > Server.MAXIMUM_USERNAME_LENGTH) {
            this.sendMessage(Protocol.alreadyLoggedInFormat());
        } else {
            // Client login accepted
            this.server.setNewClient(clientDesiredUsername, this);
            this.sendMessage(Protocol.loginFormat());
        }
    }

    /**
     * Internal method that handles the move command issued by the client.
     *
     * @param line String protocol message
     */
    private void handleMoveCommand(String line) {
        // Client wants to attempt to perform a move,
        // need to forward the client desired move to respective game handler
        // Check if the client is even in a game
        if (!this.server.getRooms().containsKey(this)) {
            return;
        }

        // Getting reference to the game room
        GameRoom gameRoom = this.server.getRooms().get(this);

        // Check if it even is the clients turn
        if (!gameRoom.getGameHandler().getGame().getPlayerTurn().username()
                .equals(this.server.getClientHandlers().get(this))) {
            return;
        }

        // Writing to the pipe input of the game handler
        gameRoom.forwardToGameHandler(line);
    }

    /**
     * Method that sends already protocol formatted message to the client socket output
     *
     * @param message String protocol message
     */
    /*@requires message != null; @*/
    public void sendMessage(String message) {
        this.clientSocketOutput.println(message);
        this.clientSocketOutput.flush();
    }
}
