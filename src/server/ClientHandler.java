package server;

import exceptions.HandshakeFailed;
import networking.Protocol;

import java.io.*;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

public class ClientHandler implements Runnable {
    /*@public invariant clientSocket != null;
      @public invariant server != null;*/

    /**
     * Holds the socket of the assigned client
     */
    private /*@spec_public; @*/ Socket clientSocket;

    /**
     * Holds the output of the client socket
     */
    private PrintWriter clientSocketOutput;

    /**
     * Holds the reference back to the server
     */
    private /*@spec_public; @*/ Server server;

    /**
     * Indicates whether the initial handshake between the client and server has been established
     * Only having established a handshake, can the client and server continue with any other communication
     */
    private boolean handshakeAcknowledged = false;

    /**
     * Holds the list of all extensions the client supports
     */
    private List<String> clientSupportedExtensions = new ArrayList<>();

    /**
     * Constructor that initializes each client handler
     *
     * @param clientSocket
     */
    /*@requires server != null;
      @requires clientSocket != null;
      @assignable server;
      @assignable clientSocket;
      @assignable clientSocketOutput;*/
    public ClientHandler(Server server, Socket clientSocket) {
        this.server = server;
        this.clientSocket = clientSocket;

        // Attempting to initialize wrappers for client IO
        // OutputStreamWriter converts the incoming chars to bytes,
        // buffered wrappers are for convenience / performance reasons
        try {
            this.clientSocketOutput = new PrintWriter(new OutputStreamWriter(clientSocket.getOutputStream()));
        } catch (IOException e) {
            //TODO: Read up on what to do in this case
        }
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        try (BufferedReader clientSocketInput = new BufferedReader(new InputStreamReader(clientSocket.getInputStream()))) {
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
        } catch (IOException e) {
            //TODO: Read up on what to do in this case
        }
    }

    /**
     * Internal method that sends acknowledgment HELLO protocol sequence to the client
     */
    private void sendAcknowledgeHandshake() {
        // Sending the handshake acknowledgment to the client
        this.sendMessage(Protocol.helloFormat(Server.SERVER_DESCRIPTION, Server.SUPPORTED_EXTENSIONS));
    }

    /**
     * Internal method that (assuming the message is actually a handshake initialization incoming from client),
     * acknowledges the handshake and updates the clients supported extensions
     *
     * @param line
     * @throws HandshakeFailed if the incoming message is not HELLO protocol adherent
     */
    /*@requires line != null;
      @assignable clientSupportedExtensions;
      @assignable handshakeAcknowledged;
      @signals_only HandshakeFailed; */
    private void acknowledgeHandshake(String line) throws HandshakeFailed {
        // Handshake is already acknowledged
        if (this.handshakeAcknowledged) return;

        // Getting the supported extensions extracted from client protocol message
        List<String> supportedExtensions = Protocol.helloExtract(line);

        // Not a valid handshake message, ignoring!
        if (supportedExtensions == null) throw new HandshakeFailed();

        // Appending all extensions that client supports (if any)
        for (String extension: supportedExtensions) {
            this.clientSupportedExtensions.add(extension);
        }

        // Sending back the handshake acknowledgment from the server,
        // providing all the extensions that the server supports
        this.sendAcknowledgeHandshake();

        // Updating state and waiting for next commands
        this.handshakeAcknowledged = true;
    }

    /**
     * Internal method that handles all incoming commands from the client
     *
     * @param line String line that we received from the server
     */
    /*@requires line != null; @*/
    private void handleIncomingCommand(String line) {
        String command = Protocol.commandExtract(line);

        switch (command) {
            case Protocol.LOGIN:
                // A user can login if the provided username is not taken
                String clientDesiredUsername = Protocol.loginExtract(line);

                System.out.println("Login request received " + clientDesiredUsername);

                // Username is taken, client has to try to login again
                if (this.server.isUsernameTaken(clientDesiredUsername)) {
                    this.sendMessage(Protocol.alreadyLoggedInFormat());
                } else {
                    // Client login accepted
                    this.server.setNewClient(clientDesiredUsername, this.clientSocket);
                    this.sendMessage(Protocol.loginFormat());
                }

            case Protocol.LIST:
                // Sends client the list of all logged in user usernames
                this.sendMessage(Protocol.listFormat(this.server.getUserUsernames()));
                break;
            default:
                // Unsupported command, 'do nothing'
        }
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
