package client;

import client.operators.MessageOperator;
import client.operators.SysoutOperator;
import exceptions.HandshakeFailed;
import networking.Protocol;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

/**
 * Client class that communicates with ClientHandler on the server,
 * and acts as a controller between Server and client GameRoom
 */
public class Client {
    /**
     * Holds the socket of the server that client has connected to
     */
    private Socket socket;

    /**
     * Holds the output of the server socket
     */
    private PrintWriter serverSocketOutput;

    /**
     * Holds the assigned message handler that will handle the incoming messages from server
     */
    private final MessageOperator messageOperator;

    /**
     * Holds and handles the current ongoing game that the client is playing (if any)
     */
    private final GameRoom gameRoom;

    /**
     * Holds the desired username of the client
     */
    private String username;

    /**
     * Indicates whether the initial handshake between the client and server has been established
     * Only having established a handshake, can the client and server continue with any other communication
     */
    private boolean handshakeEstablished = false;

    /**
     * Indicates whether the client has successfully claimed a username on the server and logged in
     */
    private boolean successfullyLoggedIn = false;

    /**
     * Holds the list of all extensions the server supports
     */
    private final List<String> serverSupportedExtensions = new ArrayList<>();

    /**
     * Stores the list of all supported extensions by the client
     */
    protected static final List<String> SUPPORTED_EXTENSIONS = new ArrayList<>();

    /**
     * Holds the description of the client
     */
    public static final String CLIENT_DESCRIPTION = "Yellow 7 Client";

    /**
     * Constructor that initializes each client and provides a default MessageHandler
     *
     * @param username String, desired client username
     */
    /*@requires username != null;
      @assignable username; */
    public Client(String username) {
        this.username = username;
        this.messageOperator = new SysoutOperator();
        this.gameRoom = new GameRoom(this);
    }

    /**
     * States whether a handshake between the client and the server (that the client has connected to) has been established
     *
     * @return true if client has connected to a server and handshake is established
     */
    /*@ensures socket != null && handshakeEstablished ==> \result == true; @*/
    public boolean isHandshakeEstablished() {
        return this.socket != null && this.handshakeEstablished;
    }

    /**
     * States whether the client has successfully logged in to the server
     *
     * @return true / false
     */
    /*@ensures socket != null && successfullyLoggedIn ==> \result == true; @*/
    public boolean isSuccessfullyLoggedIn() {
        return this.socket != null && this.successfullyLoggedIn;
    }

    /**
     * Method that allows to change client username unless they have successfully logged in
     *
     * @param desiredUsername String, desired username of client
     */
    /*@requires desiredUsername != null && desiredUsername != username;
      @requires !successfullyLoggedIn;
      @assignable username; @*/
    public void setUsername(String desiredUsername) {
        if (this.isSuccessfullyLoggedIn()) return;

        this.username = desiredUsername;
    }

    /**
     * Method that returns the username of the client
     *
     * @return String client username
     */
    /*@pure; @*/
    public String getUsername() {
        return this.username;
    }

    /**
     * Method that returns the message handler attached to the client
     *
     * @return MessageHandler instance
     */
    /*@pure; @*/
    public MessageOperator getMessageOperator() {
        return this.messageOperator;
    }

    /**
     * Method that returns the GameRoom attached to the client
     *
     * @return GameRoom instance
     */
    /*@pure; @*/
    protected GameRoom getGameRoom() {
        return this.gameRoom;
    }

    /**
     * Method that attempts to connect the client to a socket server
     *
     * @param address InetAddress of the target server
     * @param port    int of the target server
     * @return true / false indicating if the action was successful
     */
    /*@requires address != null;
      @requires port > 0 && port < 65535;*/
    public boolean connect(InetAddress address, int port) {
        // Attempting to connect and initialize the socket and IO
        try {
            this.socket = new Socket(address, port);
            this.serverSocketOutput = new PrintWriter(new OutputStreamWriter(this.socket.getOutputStream()));
        } catch (IOException e) {
            return false;
        }

        // Starting the handshake with server automatically
        this.sendInitializeHandshake();

        // 'Listening' for incoming commands,
        // assigning new thread for it, to not block the main calling one
        new Thread(() -> {
            try (BufferedReader socketInputReader = new BufferedReader(new InputStreamReader(this.socket.getInputStream()))) {
                // Reading line by line
                String line;

                while ((line = socketInputReader.readLine()) != null) {
                    // Attempting to finalize the handshake
                    try {
                        // Attempting to automatically log in with the desired username after having established a handshake
                        // It's possible that server will deny our username, therefore we will need to handle that case
                        this.handleIncomingHandshake(line);
                    } catch (HandshakeFailed e) {
                        // After sending initial handshake message,
                        // the only command we can expect from the server is acknowledgment
                        continue;
                    }

                    // Handling all incoming commands
                    handleIncomingCommand(line);
                }

                this.close();
            } catch (IOException e) {
                this.close();
            }
        }).start();

        return true;
    }

    /**
     * Internal method that closes the client connection
     */
    private void close() {
        try {
            this.socket.close();
        } catch (IOException ignored) {}
    }

    /**
     * Internal method that attempts to log in into the server
     */
    /*@requires !successfullyLoggedIn; @*/
    private void attemptLogin() {
        // Checking if the client is already logged in
        if (this.isSuccessfullyLoggedIn()) return;

        this.sendMessage(Protocol.loginFormat(this.username));
    }

    /**
     * Method that re-assigns the client username and attempts to log in again, if not already logged in
     *
     * @param newUsername String new desired username
     */
    /*@requires !successfullyLoggedIn; @*/
    public void attemptLogin(String newUsername) {
        this.setUsername(newUsername);
        this.attemptLogin();
    }

    /**
     * Internal method that starts handshake initialization with the server
     */
    /*@requires !isHandshakeEstablished(); @*/
    private void sendInitializeHandshake() {
        this.sendMessage(Protocol.helloFormat(Client.CLIENT_DESCRIPTION, Client.SUPPORTED_EXTENSIONS));
    }

    /**
     * Method that joins the player queue waiting for a game, if the client is already in the queue,
     * calling this method again will remove him from it
     */
    public void joinQueue() {
        this.sendMessage(Protocol.queueFormat());
    }

    /**
     * Method that forwards clients desired move to the server for verification
     *
     * @param location int, location index on board
     */
    /*@requires location >= 0 && location <= 64; */
    public void attemptMove(int location) {
        this.sendMessage(Protocol.moveFormat(location));
    }

    /**
     * Method that inquiries the server about the list of connected client usernames
     */
    public void queryUserList() {
        this.sendMessage(Protocol.listFormat());
    }

    /**
     * Internal method that (assuming the message is actually a handshake acknowledgment incoming from server),
     * handles the handshake and updates the servers supported extensions
     *
     * @param line String line that we received from the server
     * @throws HandshakeFailed if the incoming message is not HELLO protocol adherent
     */
    /*@requires line != null;
      @requires !handshakeEstablished;
      @assignable handshakeEstablished;
      @signals_only HandshakeFailed; */
    private void handleIncomingHandshake(String line) throws HandshakeFailed {
        // Handshake is already established
        if (this.isHandshakeEstablished()) return;

        // Getting the supported extensions extracted from server protocol message
        List<String> supportedExtensions = Protocol.helloExtract(line);

        // Not a valid handshake acknowledgment from server,
        // why did the server message us? ignoring!
        if (supportedExtensions == null) throw new HandshakeFailed();

        // Appending all extensions that server supports (if any)
        this.serverSupportedExtensions.addAll(supportedExtensions);

        // Updating state
        this.handshakeEstablished = true;

        // Automatically attempting to log in
        this.attemptLogin();
    }

    /**
     * Internal method that handles all incoming commands from the server client handler to the client
     *
     * @param line String line that we received from the server
     */
    /*@requires line != null; @*/
    private void handleIncomingCommand(String line) {
        String command = Protocol.commandExtract(line);

        switch (command) {
            // We have received indication from the server that login was successful
            case Protocol.LOGIN -> {
                this.successfullyLoggedIn = true;
                this.messageOperator.incomingMessage(SysoutOperator.SUCCESS + " Successfully logged in!");
            }
            case Protocol.ALREADY_LOGGED_IN -> {
                this.successfullyLoggedIn = false;
                this.messageOperator.incomingMessage(SysoutOperator.ERROR + " A user with the provided username already exists!");
            }
            case Protocol.LIST -> this.messageOperator.incomingMessage(SysoutOperator.INFO + " Online users: " + Protocol.listExtract(line));
            case Protocol.ERROR -> this.messageOperator.incomingMessage(SysoutOperator.ERROR + " Provided move is invalid!");
            // All game related things are forwarded to the GameHandler
            case Protocol.NEWGAME, Protocol.MOVE, Protocol.GAMEOVER -> this.gameRoom.forwardToGameHandler(line);
        }
    }


    /**
     * Method that sends already protocol formatted message to the server socket output
     *
     * @param message String protocol message
     */
    public void sendMessage(String message) {
        this.serverSocketOutput.println(message);
        this.serverSocketOutput.flush();
    }
}
