package server;

import client.Client;
import game.BoardGame;
import game.players.Player;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.*;
import java.util.stream.Collectors;

public class Server {
    /*@public invariant (\forall int i; i > 0 && i < queue.size();
        (\exists int j; j > 0 && j < users.size(); queue.get(i).equals(users.get(j)))); @*/

    /*@public invariant (\exists int j, k; j > 0 && k > 0 && j < users.size() && k < users.size();
        rooms.keySet().contains(users.get(j).getUsername() + users.get(k).getUsername()));*/

    /**
     * Stores the servers socket
     */
    private ServerSocket serverSocket;

    /**
     * Stores client handler to client username pairs
     */
    private Map<ClientHandler, String> clientHandlers = new HashMap<>();

    /**
     * Stores client username to client handler pairs
     */
    private Map<String, ClientHandler> clientHandlersReverse = new HashMap<>();

    /**
     * Stores room name to board game pairs
     * Room name consists of the combination of both player usernames
     */
    protected /*@spec_public; @*/ Map<String, BoardGame> rooms = new HashMap<>();

    /**
     * Stores username to player pairs
     */
    private /*@spec_public; @*/ Map<String, Player> users = new HashMap<>();

    /**
     * Stores the list of all player usernames that are in the queue
     */
    protected  /*@spec_public; @*/ List<String> queue = new ArrayList<>();

    /**
     * Stores the list of all supported extensions by the server
     */
    protected static final List<String> SUPPORTED_EXTENSIONS = new ArrayList<>();

    /**
     * Holds the description of the server
     */
    public static final String SERVER_DESCRIPTION = "Yellow 7 Server";

    /**
     * Method that returns the set of all connected user usernames on the server
     * @return
     */
    /*@pure; @*/
    public Set<String> getUserUsernames() {
        return this.users.keySet();
    }

    /**
     * Method that indicates whether a provided username is available on the server
     * @param username String, desired username
     * @return true / false
     */
    /*@pure; @*/
    public boolean isUsernameTaken(String username) {
        return this.users.containsKey(username);
    }

    /**
     * Method that initializes mappings between client username and it's handler
     * @param username String, username of the authenticated client
     * @param clientHandler ClientHandler allocated to that client connection
     */
    public void setNewClient(String username, ClientHandler clientHandler) {
        this.users.put(username, null); // TODO: Consider the keeping track of users implementation
        this.clientHandlers.put(clientHandler, username);
        this.clientHandlersReverse.put(username, clientHandler);
    }

    /**
     * Method that adds user to the queue, removes from the queue if already in the queue.
     * Synchronized since could experience concurrency problems by one of the ClientHandler threads
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
            this.queue.notify();
        }
    }

    /**
     * Method that returns the list of client usernames that are in waiting queue for a game
     */
    public List<String> getQueue() {
        return this.queue;
    }

    public Map<String, BoardGame> getRooms() {
        return this.rooms;
    }

    /**
     * Method that attempts to start the server on a 'randomly' assigned port
     * @return true / false indicating if the action was successful
     */
    /*@assignable serverSocket; @*/
    //TODO: Read best and most proper thread and socket termination practices
    public boolean start() {
        // Attempting to initialize server socket
        try {
            this.serverSocket = new ServerSocket(0);
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
                    Socket clientSocket = this.serverSocket.accept();
                    // Creating a handler that will handle this connection
                    ClientHandler clientSocketHandler = new ClientHandler(this, clientSocket);
                    // Creating a new separate thread for this client handler
                    new Thread(clientSocketHandler).start();
                } catch (IOException e) {
                    // TODO: Handle the exception
                }
            }
        }).start();

        // Queue thread that handles match creation
        new Thread(new QueueHandler(this)).start();

        // Everything was a success
        return true;
    }

    /**
     * Method that broadcasts already formatted message according to the protocol in a specific game room
     */
    public void broadCastMessage(String roomName, String message) {
        // Check if a game associated with the provided room name exists
        BoardGame roomGame = this.rooms.get(roomName);

        // Room game not found
        if (roomGame == null) return;

        // Otherwise getting all room player usernames
        List<String> roomUsernames = roomGame.getPlayers()
                                    .stream()
                                    .map(player -> player.getUsername())
                                    .collect(Collectors.toList());

        // Going over all usernames
        for (String username: roomUsernames) {
            // Getting clients handler and forwarding the message
            ClientHandler clientHandler = this.clientHandlersReverse.get(username);
            clientHandler.sendMessage(message);
        }
    }

    /**
     * Method that retrieves the port that the server is currently running on
     *
     * @return
     */
    /*@requires serverSocket != null;
      @ensures \result > 0 && \result < 65535;
      @pure;*/
    public int getPort() {
        return this.serverSocket.getLocalPort();
    }
}
