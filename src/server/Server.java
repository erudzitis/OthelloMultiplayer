package server;

import networking.Protocol;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;

public class Server {
    /*@public invariant (\forall int i; i > 0 && i < queue.size();
        (\exists int j; j > 0 && j < users.size(); queue.get(i).equals(users.get(j)))); @*/

    /**
     * Stores the servers socket
     */
    private ServerSocket serverSocket;

    /**
     * Stores client handler to client username pairs
     */
    private final Map<ClientHandler, String> clientHandlers = new HashMap<>();

    /**
     * Stores client username to client handler pairs
     */
    private final Map<String, ClientHandler> clientHandlersReverse = new HashMap<>();

    /**
     * Stores client handler to board game room pairs
     */
    protected final /*@spec_public; @*/ Map<ClientHandler, GameRoom> rooms = new HashMap<>();

    /**
     * Stores connected client usernames
     */
    private final /*@spec_public; @*/ List<String> users = new ArrayList<>();

    /**
     * Stores the list of all player usernames that are in the queue
     */
    protected final /*@spec_public; @*/ List<String> queue = new ArrayList<>();

    /**
     * Stores the list of all supported extensions by the server
     */
    protected static final List<String> SUPPORTED_EXTENSIONS = new ArrayList<>();

    /**
     * Holds the description of the server
     */
    public static final String SERVER_DESCRIPTION = "Yellow 7 Server";

    /**
     * Holds the length of maximum supported username for clients
     */
    protected static final int MAXIMUM_USERNAME_LENGTH = 30;

    /**
     * Method that returns the list of all connected user usernames on the server
     *
     * @return Set<String> of connected client usernames
     */
    /*@pure; @*/
    public List<String> getUserUsernames() {
        return this.users;
    }

    /**
     * Method that indicates whether a provided username is available on the server
     *
     * @param username String, desired username
     * @return true / false
     */
    /*@pure; @*/
    public boolean isUsernameTaken(String username) {
        return this.users.contains(username);
    }

    /**
     * Synchronized method that initializes mappings between client username and its handler
     *
     * @param username      String, username of the authenticated client
     * @param clientHandler ClientHandler allocated to that client connection
     */
    public void setNewClient(String username, ClientHandler clientHandler) {
        synchronized (this.users) {
            this.clientHandlers.put(clientHandler, username);
            this.clientHandlersReverse.put(username, clientHandler);
            this.users.add(username);
        }
    }

    /**
     * Method that adds user to the queue, removes from the queue if already in the queue.
     * Synchronized since could experience concurrency problems by one of the ClientHandler threads
     *
     * @param clientHandler ClientHandler of the particular client
     */
    public void setQueue(ClientHandler clientHandler) {
        synchronized (this.queue) {
            // Getting the user username
            String clientUsername = this.clientHandlers.get(clientHandler);

            // Check if the client even exists?
            if (clientUsername == null) return;

            // Check if the user is already in the queue
            if (this.queue.contains(clientUsername)) {
                this.queue.remove(clientUsername);
            } else {
                this.queue.add(clientUsername);
            }

            // Notifying 'queue' thread
            this.queue.notifyAll();
        }
    }

    /**
     * Method that returns the list of client usernames that are in waiting queue for a game
     *
     * @return List<String> of client usernames
     */
    public List<String> getQueue() {
        return this.queue;
    }

    /**
     * Method that returns the map of ongoing match room names and their associated rooms
     *
     * @return Map<String, BoardGame>
     */
    public Map<ClientHandler, GameRoom> getRooms() {
        return this.rooms;
    }

    /**
     * Method that returns the map of assigned client handlers and corresponding client usernames
     *
     * @return Map<String, ClientHandler>
     */
    protected Map<ClientHandler, String> getClientHandlers() {
        return this.clientHandlers;
    }

    /**
     * Method that returns the map of existing client usernames and their assigned client handlers
     *
     * @return Map<String, ClientHandler>
     */
    protected Map<String, ClientHandler> getClientHandlersReverse() {
        return this.clientHandlersReverse;
    }

    /**
     * Synchronized method that handles the disconnection of a client by informing any other dependant objects
     *
     * @param clientHandler ClientHandler instance that was assigned to the disconnected client socket
     */
    protected void clientDisconnected(ClientHandler clientHandler) {
        // Attempting to get hold of the client reference
        String clientUsername = this.clientHandlers.get(clientHandler);

        // Client doesn't appear to exist
        if (clientUsername == null) return;

        // Attempting to get the reference to the GameRoom that the client is in
        GameRoom clientGameRoom = this.rooms.get(clientHandler);

        // If the client was in a game, inform the game handler
        if (clientGameRoom != null) {
            synchronized (clientGameRoom) {
                // Informing game handler of termination
                clientGameRoom.forwardToGameHandler(Protocol.clientDisconnectedFormat(clientUsername));

                // Need to wait until message is forwarded back to clients and room cleanup is performed
                while (!clientGameRoom.getGameHandler().isCleanupPerformed()) {
                    try {
                        clientGameRoom.wait();
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                }
            }

            // Closing the game room
            clientGameRoom.close();
        }

        // Removing all other associations
        this.users.remove(clientUsername);
        this.clientHandlers.remove(clientHandler);
        this.clientHandlersReverse.remove(clientUsername);
    }

    /**
     * Synchronized method that cleans up fields related to client username game rooms
     *
     * @param clientUsernames List<String> of client usernames
     */
    protected void cleanUpGameRoom(List<String> clientUsernames) {
        synchronized (this.rooms) {
            for (String clientUsername : clientUsernames) {
                this.rooms.remove(this.clientHandlersReverse.get(clientUsername));
            }
        }
    }

    /**
     * Internal method that attempts to accept client and initialize a client handler for it
     * @param clientSocket Socket of the client that wants to connect to the server
     */
    private void acceptClient(Socket clientSocket) {
        try {
            // Creating a handler that will handle this connection
            ClientHandler clientSocketHandler = new ClientHandler(this, clientSocket);
            // Creating a new separate thread for this client handler
            new Thread(clientSocketHandler).start();
        } catch (IOException ignored) {
            // There was IOException when attempting to create a client handler, we ignore this client connection attempt
        }
    }

    /**
     * Method that attempts to start the server on a 'randomly' assigned port
     *
     * @return true / false indicating if the action was successful
     */
    /*@assignable serverSocket; @*/
    public boolean start() {
        // Attempting to initialize server socket
        try {
            this.serverSocket = new ServerSocket(8000);
        } catch (IOException e) {
            return false;
        }

        // Server socket has been initialized,
        // we need to listen to any possible incoming client connections,
        // however this is a blocking method, so we allocate a new thread for it
        new Thread(() -> {
            // Listening for incoming connections 'endlessly'
            while (true) {
                try {
                    // New client connection received
                    this.acceptClient(this.serverSocket.accept());
                } catch (IOException e) {
                    Thread.currentThread().interrupt();
                }
            }
        }).start();

        // Queue thread that handles match creation
        new Thread(new QueueHandler(this)).start();

        // Everything was a success
        return true;
    }

    /**
     * Method that broadcasts already formatted message according to the protocol to specific clients
     *
     * @param message   String formatted protocol message
     * @param usernames List<String> of client usernames
     */
    /*@requires message != null && usernames.size() > 0;
      @requires (\forall int i; i >= 0 && i < usernames.size(); users.contains(usernames.get(i))); */
    public void broadCastMessage(String message, List<String> usernames) {
        // Going over all usernames
        for (String username : usernames) {
            // Getting clients handler and forwarding the message
            ClientHandler clientHandler = this.clientHandlersReverse.get(username);

            // A client handler must exist
            if (clientHandler == null) return;

            clientHandler.sendMessage(message);
        }
    }

    /**
     * Method that broadcasts already formatted message according to the protocol to specific clients
     *
     * @param message   String formatted protocol message
     * @param usernames String vararg
     */
    public void broadCastMessage(String message, String... usernames) {
        broadCastMessage(message, Arrays.asList(usernames));
    }

    /**
     * Method that retrieves the port that the server is currently running on
     *
     * @return int, port number between 0 and 65535
     */
    /*@requires serverSocket != null;
      @ensures \result > 0 && \result < 65535;
      @pure;*/
    public int getPort() {
        return this.serverSocket.getLocalPort();
    }

    /**
     * Method that indicates whether the server instance is running
     * @return true / false
     */
    protected boolean isRunning() {
        return this.serverSocket != null && !this.serverSocket.isClosed();
    }

    /**
     * Starts the server instance
     *
     * @param args command line args --ignored
     */
    public static void main(String[] args) {
        Server server = new Server();

        if (server.start()) {
            System.out.println("Server successfully listening on port " + server.getPort());
        }
    }
}
