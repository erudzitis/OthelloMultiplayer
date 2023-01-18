package server;

import game.BoardGame;
import game.players.Player;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
     * Stores username to client socket pairs
     */
    private Map<String, Socket> clientSockets;

    /**
     * Stores room name to board game pairs
     * Room name consists of the combination of both player usernames
     */
    private /*@spec_public; @*/ Map<String, BoardGame> rooms;

    /**
     * Stores username to player pairs
     */
    private /*@spec_public; @*/ Map<String, Player> users;

    /**
     * Stores the list of all player usernames that are in the queue
     */
    private /*@spec_public; @*/ List<String> queue;

    /**
     * Stores the list of all supported extensions by the server
     */
    protected static final List<String> SUPPORTED_EXTENSIONS = new ArrayList<>();

    /**
     * Holds the description of the server
     */
    public static final String SERVER_DESCRIPTION = "Yellow 7 Server";

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

        // Everything was a success
        return true;
    }

    /**
     * Method that broadcasts already formatted message according to the protocol in a specific game room
     */
    /*@requires game != null && message != null; @*/
    public void broadCastMessage(BoardGame game, String message) {
        //TODO: Implement
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
