package client;

import exceptions.HandshakeFailed;
import game.BoardGame;
import networking.Protocol;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;

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
     * Holds and keeps track of the current ongoing game that the client is playing (if any)
     */
    private BoardGame game;

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
    private List<String> serverSupportedExtensions = new ArrayList<>();

    /**
     * Stores the list of all supported extensions by the client
     */
    public static final List<String> SUPPORTED_EXTENSIONS = new ArrayList<>();

    /**
     * Holds the description of the client
     */
    public static final String CLIENT_DESCRIPTION = "Yellow 7 Client";

    /**
     * Constructor that initializes each client
     *
     * @param username String, desired client username
     */
    /*@requires username != null;
      @assignable username;*/
    public Client(String username) {
        this.username = username;
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
     * @return
     */
    /*@ensures socket != null && successfullyLoggedIn ==> \result == true; @*/
    public boolean isSuccessfullyLoggedIn() {
        return this.socket != null && this.successfullyLoggedIn;
    }

    /**
     * Method that returns the username of the client
     * @return
     */
    public String getUsername() {
        return this.username;
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
                        // Attempting to automatically login with the desired username after having established a handshake
                        // It's possible that server will deny our username, therefore we will need to handle that case
                        this.handleIncomingHandshake(line);
                    } catch (HandshakeFailed e) {
                        // After sending initial handshake message,
                        // the only command we can expect from the server is acknowledgment
                        continue;
                    }

                    // Handling all incoming commands
                    handleIncomingCommand(line);

                    //TODO: Implement incoming command handling on client
                }
            } catch (IOException e) {
                //TODO: Read up on what to do in this case
            }
        }).start();

        return true;
    }

    /**
     * Internal method that attempts to login into the server
     */
    /*@requires !successfullyLoggedIn; @*/
    private void attemptLogin() {
        // Checking if the client is already logged in
        if (this.successfullyLoggedIn) return;

        this.sendMessage(Protocol.loginFormat(this.username));
    }

    /**
     * Internal method that starts handshake initialization with the server
     */
    private void sendInitializeHandshake() {
        this.sendMessage(Protocol.helloFormat(Client.CLIENT_DESCRIPTION, Client.SUPPORTED_EXTENSIONS));
    }

    /**
     * Internal method that joins the player queue waiting for a game, if the client is already in the queue,
     * calling this method again will remove him from it
     */
    private void joinQueue() {
        this.sendMessage(Protocol.queueFormat());
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
      @assignable serverSupportedExtensions;
      @assignable handshakeEstablished;
      @signals_only HandshakeFailed; */
    private void handleIncomingHandshake(String line) throws HandshakeFailed {
        // Handshake is already established
        if (this.handshakeEstablished) return;

        // Getting the supported extensions extracted from server protocol message
        List<String> supportedExtensions = Protocol.helloExtract(line);

        // Not a valid handshake acknowledgment from server,
        // why did the server message us? ignoring!
        if (supportedExtensions == null) throw new HandshakeFailed();

        // Appending all extensions that server supports (if any)
        for (String extension : supportedExtensions) {
            this.serverSupportedExtensions.add(extension);
        }

        // Updating state
        this.handshakeEstablished = true;

        // Automatically attempting to login
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
            case Protocol.LOGIN:
                // We have received indication from the server that login was successful
                this.successfullyLoggedIn = true;
                break;
            case Protocol.ALREADYLOGGEDIN:
                // A user with the username that we provided is already logged in
                this.successfullyLoggedIn = false;
                //TODO: Implement a way to ask user again for a new username and attempt to login
                break;
            case Protocol.LIST:
                //TODO: Forward the list of online users somewhere
                break;
            default:
                // Unsupported command, 'do nothing'
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
