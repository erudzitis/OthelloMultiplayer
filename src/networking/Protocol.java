package networking;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

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
    public static final String HELLO = "HELLO";
    public static final String LOGIN = "LOGIN";
    public static final String SEPERATOR = "~";
    public static final String ALREADYLOGGEDIN = "ALREADYLOGGEDIN";
    public static final String LIST = "LIST";
    public static final String QUEUE = "QUEUE";
    public static final String NEWGAME = "NEWGAME";
    public static final String MOVE = "MOVE";
    public static final String GAMEOVER = "GAMEOVER";
    public static final String ERROR = "ERROR";

    public static final String DISCONNECT = "DISCONNECT";
    public static final String VICTORY = "VICTORY";
    public static final String DRAW = "DRAW";

    /**
     * Enforcing the constructor to be private, so no instances could be made
     */
    private Protocol() {}

    /**
     * Method that returns an array of protocol message 'contents'
     *
     * @param message String protocol message
     * @return String[] message 'contents'
     */
    public static String[] split(String message) {
        return message.split(SEPERATOR);
    }

    /**
     * Method that extracts the main protocol method out of protocol message
     *
     * @param message String protocol message
     * @return String main protocol command
     */
    public static String commandExtract(String message) {
        return split(message)[0];
    }

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
    public static String helloFormat(String description, List<String> extensions) {
        // Formatting the main protocol message part
        StringBuilder protocolMessageBuilder = new StringBuilder(HELLO + SEPERATOR + description);
        // Adding all extensions, if any
        for (String extension: extensions) protocolMessageBuilder.append(SEPERATOR + extension);

        return protocolMessageBuilder.toString();
    }

    /**
     * Method that formats hello protocol message and extracts all supported extensions
     *
     * @param message String protocol HELLO message
     * @return null if the protocol message is not HELLO, List<String> supported extensions otherwise
     */
    public static List<String> helloExtract(String message) {
        String[] messageSplit = split(message);
        String messageHello = messageSplit[0];

        // Checking if message adheres to the protocol
        if (!messageHello.equals(HELLO)) return null;

        // Checking if there are even any extensions
        if (messageSplit.length == 2) return new ArrayList<>();

        // Otherwise, all extensions (if any) are found after description
        String[] extensions = Arrays.copyOfRange(messageSplit, 2, messageSplit.length);

        return new ArrayList<>(Arrays.asList(extensions));
    }

    /**
     * Method that generates String message that gets sent from the client in 'login' process when choosing a username.
     *
     * LOGIN~<username>
     *
     * @param username String, desired username
     * @return String formatted message
     */
    public static String loginFormat(String username) {
        return LOGIN + SEPERATOR + username;
    }

    /**
     * Method that extracts the provided user username from logic protocol message
     *
     * @param message String protocol message
     * @return String, user provided username
     */
    public static String loginExtract(String message) {
        return split(message)[1];
    }

    /**
     * Method that generates String message for server that gets sent back to client to indicate a successful login
     *
     * LOGIN
     * .
     * @return String formatted message
     */
    public static String loginFormat() {
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
    public static String alreadyLoggedInFormat() {
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
    public static String listFormat() {
        return LIST;
    }

    /**
     * Method that generates String message for server that responds to LIST command from client.
     * Lists the different usernames that are currently logged into the server, including the requesting client.
     *
     * LIST[~username]*
     *
     * @param usernames Collection<String> Collection of usernames of people that are connected to the server
     * @return String formatted message
     */
    public static String listFormat(Collection<String> usernames) {
        // Formatting the main protocol message part
        StringBuilder protocolMessageBuilder = new StringBuilder(LIST);
        // Adding all usernames
        for (String username: usernames) protocolMessageBuilder.append(SEPERATOR + username);

        return protocolMessageBuilder.toString();
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
    public static String queueFormat() {
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
    public static String newGameFormat(String username1, String username2) {
        return NEWGAME + SEPERATOR + username1 + SEPERATOR + username2;
    }

    /**
     * Method that formats newgame protocol message and extracts all client usernames associated to the new game
     * @param message
     * @return
     */
    public static List<String> newGameExtract(String message) {
        String[] messageSplit = split(message);
        String[] clientUsernames = Arrays.copyOfRange(messageSplit, 1, messageSplit.length);

        return new ArrayList<>(Arrays.asList(clientUsernames));
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
    public static String moveFormat(int location) {
        return MOVE + SEPERATOR + location;
    }

    /**
     * Method that formats move protocol message and extracts int location of the move
     * @param message
     * @return
     */
    public static int moveExtract(String message) {
        return Integer.valueOf(split(message)[1]);
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
    public static String gameOverFormat(String reason, String winner) {
        return GAMEOVER + SEPERATOR + reason + ((winner == null) ? "" : SEPERATOR + winner);
    }

    /**
     * Method that generates String message for server to respond to a client query indicating that it's invalid
     *
     * ERROR
     *
     * @return String formatted message
     */
    public static String errorFormat() {
        return ERROR;
    }
}
