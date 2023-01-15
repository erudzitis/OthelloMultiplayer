package networking;

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

/**
 * Networking protocol used by the server and client for interchangeable communication.
 * The different arguments of commands are separated by a tilde ("~").
 *
 * <argument> required argument.
 * <argument>^n required argument precisely n times.
 * [argument] optional input or argument.
 * [argument]* optional input or argument 0 or more times.
 * [argument]+ optional input or argument 1 or more times.
 */
public class Protocol {
    private static final String HELLO = "HELLO";
    private static final String LOGIN = "LOGIN";
    private static final String SEPERATOR = "~";
    private static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    private static final String LIST = "LIST";
    private static final String QUEUE = "QUEUE";
    private static final String NEWGAME = "NEWGAME";
    private static final String MOVE = "MOVE";
    private static final String GAMEOVER = "GAMEOVER";
    private static final String ERROR = "ERROR";

    public static final String DISCONNECT = "DISCONNECT";
    public static final String VICTORY = "VICTORY";
    public static final String DRAW = "DRAW";

    /**
     * Method that generates String for initial message that gets sent from the client after establishing connection,'
     * or sent as response from the server.
     *
     * HELLO~<client description>[~extension]*
     *
     * @param description String, descriptive representation of the server / client
     * @param extensions List<String> supported extensions by the server / client
     * @return String formatted message
     */
    public String hello(String description, List<String> extensions) {
        // Formatting the main protocol message part
        String protocolMessage = HELLO + SEPERATOR + description;
        // Adding all extensions, if any
        for (String extension: extensions) protocolMessage += SEPERATOR + extension;

        return protocolMessage;
    }

    /**
     * Method that generates String message that gets sent from the client in 'login' process when choosing a username.
     *
     * LOGIN~<username>
     *
     * @param username String, desired username
     * @return String formatted message
     */
    public String login(String username) {
        return LOGIN + SEPERATOR + username;
    }

    /**
     * Method that generates String message for server that gets sent back to client to indicate a successful login
     *
     * LOGIN
     * .
     * @return String formatted message
     */
    public String login() {
        return LOGIN;
    }

    /**
     * Method that generates String message for server that gets sent back to client to indicate
     * that a user with the previously provided username is already logged in.
     *
     * ALREADYLOGGEDIN
     *
     * @return String formatted message
     */
    public String alreadyLoggedIn() {
        return ALREADYLOGGEDIN;
    }

    /**
     * Method that generates String message for client that requests a list of clients who are currently logged into the server.
     * Allowed at any point once the client is logged in, including during a game.
     *
     * LIST
     *
     * @return String formatted message
     */
    public String list() {
        return LIST;
    }

    /**
     * Method that generates String message for server that responds to LIST command from client.
     * Lists the different usernames that are currently logged into the server, including the requesting client.
     *
     * LIST[~username]*
     *
     * @param usernames List<String> List of usernames of people that are connected to the server
     * @return String formatted message
     */
    public String list(List<String> usernames) {
        // Formatting the main protocol message part
        String protocolMessage = LIST;
        // Adding all usernames
        for (String username: usernames) protocolMessage += SEPERATOR + username;

        return protocolMessage;
    }

    /**
     * Method that generates String message for client that wants to indicate the server for joining the queue.
     * The server will place the client at the back of the queue of waiting players.
     * When the command is issued a second time, the client is removed from the queue.
     * The server does not send a reply.
     *
     * QUEUE
     *
     * @return String formatted message
     */
    public String queue() {
        return QUEUE;
    }

    /**
     * Method that generates String message for server that informs all users that were put into a new game.
     *
     * NEWGAME~<player1 name>~<player2 name>
     *
     * @param username1 String, username of the first player that was placed into the game
     * @param username2 String, username of the second player that was placed into the game
     * @return String formatted message
     */
    public String newGame(String username1, String username2) {
        return NEWGAME + SEPERATOR + username1 + SEPERATOR + username2;
    }

    /**
     * Method that generates String message for client, when client wants to indicate the server which move he desires to perform,
     * or for server that forwards the performed move to all clients in a game.
     * If location == 64, it represents a passing move.
     *
     * MOVE~<N>
     *
     * @param location int, location on board
     * @return String formatted message
     */
    public String move(int location) {
        return MOVE + SEPERATOR + location;
    }

    /**
     * Method that generates String message for server to indicate all clients in a game that a game is over.
     *
     * GAMEOVER~<reason>[~winner]
     *
     * @param reason DISCONNECT or VICTORY or DRAW
     * @param winner
     * @return String formatted message
     */
    public String gameOver(String reason, String winner) {
        return GAMEOVER + SEPERATOR + reason + (Objects.isNull(winner) ? "" : SEPERATOR + winner);
    }

    /**
     * Method that generates String message for server to respond to a client query indicating that it's invalid
     *
     * ERROR
     *
     * @return String formatted message
     */
    public String error() {
        return ERROR;
    }
}
