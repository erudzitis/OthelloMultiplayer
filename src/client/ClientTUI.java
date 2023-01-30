package client;

import client.exceptions.GameNotFoundException;
import client.exceptions.GameTurnViolationException;
import client.handlers.MessageHandler;
import client.handlers.SysoutHandler;
import client.ui.SysUtility;
import client.exceptions.InvalidMoveException;
import game.board.AlgebraicNotationConversionFailed;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Map;

public class ClientTUI {
    /**
     * Constants of supported client ui commands
     */
    private static final String LIST = "list";
    private static final String QUEUE = "queue";
    private static final String MOVE = "move";
    private static final String SKIP = "skip";
    private static final String HINT = "hint";
    private static final String HELP = "help";

    /**
     * Holds the entries of all supported TUI commands and their corresponding descriptions
     */
    private static final Map<String, String> TUI_COMMANDS = Map.ofEntries(
            Map.entry(LIST, "Lists the list of client usernames that have connected to the server"),
            Map.entry(QUEUE, "Joins the player queue / leaves the queue if entered twice"),
            Map.entry(MOVE + " [Algebraic Notation]", "Attempts to perform the move while in a game. For example, move A5. If empty move command is provided, move is skipped"),
            Map.entry(SKIP, "Skips the game turn while in a game"),
            Map.entry(HINT, "Outputs the list of possible moves in a game")
    );

    /**
     * Internal helper method that displays line separator in the TUI
     */
    private static void printSeparator() {
        System.out.println("──────────────────────────────────────────────────────────────────────────────────────────────────");
    }

    /**
     * Method that prints out the manual of the TUI supported commands
     */
    public static void printManual() {
        System.out.println(SysoutHandler.IDEA + " List of available commands, type 'help' for this menu: ");
        printSeparator();
        for (Map.Entry<String, String> command : TUI_COMMANDS.entrySet()) {
            System.out.println(command.getKey() + " : " + command.getValue());
        }
        printSeparator();
    }

    /**
     * Method that prints out the welcome message of the client
     */
    public static void printWelcome() {
        System.out.println("────────── [ " + Client.CLIENT_DESCRIPTION + " ] ──────────");
    }

    /**
     * Helper method that acquires valid server address from user
     *
     * @return InetAddress address of the server
     */
    public static InetAddress getServerAddress(SysUtility sysUtility) {
        String serverAddress = sysUtility.readString("⚙ Enter server IP address to connect to ➨ ");
        InetAddress serverAddressTranslated = null;

        // Invalid server address provided
        while (serverAddressTranslated == null) {
            try {
                serverAddressTranslated = InetAddress.getByName(serverAddress);
            } catch (UnknownHostException e) {
                serverAddress = sysUtility.readString("⚙ Invalid IP address, try again ➨ ");
            }
        }

        return serverAddressTranslated;
    }

    /**
     * Helper method that acquires server port from user
     *
     * @return int, server port
     */
    public static int getServerPort(SysUtility sysUtility) {
        return Math.min(sysUtility.readInteger("⚙ Enter server port number to connect to ➨ "), 65535);
    }

    /**
     * Helper method that acquires desired usernames and creates client instance
     *
     * @return Client
     */
    public static Client createClient(SysUtility sysUtility) {
        return new Client(sysUtility.readString(SysoutHandler.KEY + " Enter desired username ➨ "));
    }

    /**
     * Helper method that makes sure that client successfully connects to a server
     *
     * @param client Client instance to connect to the server
     */
    public static void connectClient(Client client, SysUtility sysUtility) throws InterruptedException {
        InetAddress serverAddress = getServerAddress(sysUtility);
        int serverPort = getServerPort(sysUtility);
        boolean connected = client.connect(serverAddress, serverPort);

        // Waiting for the command to go through
        // TODO: There might be a better way
        Thread.sleep(1000);

        // If client couldn't connect to the provided server, we ask for address and port again
        while (!connected) {
            client.getMessageHandler().incomingMessage(SysoutHandler.ERROR + " Couldn't connect to the server, try again!");
            serverAddress = getServerAddress(sysUtility);
            serverPort = getServerPort(sysUtility);
            connected = client.connect(serverAddress, serverPort);
        }
    }

    /**
     * Helper method that makes sure that client's username was accepted by the server and client successfully logs in,
     * assigns the accepted username in client GameHandler
     *
     * @param client Client instance to ensure the successful login
     */
    public static void ensureLogin(Client client, SysUtility sysUtility) throws InterruptedException {
        while (!client.isSuccessfullyLoggedIn()) {
            // Waiting for the command to go through
            // TODO: There might be a better way to do it
            Thread.sleep(1000);

            if (client.isSuccessfullyLoggedIn()) break;

            client.attemptLogin(sysUtility.readString(SysoutHandler.LOCK + " Username taken, try again ➨ "));
        }
    }

    public static void handleCommand(Client client, String command) {
        MessageHandler messageHandler = client.getMessageHandler();
        GameHandler gameHandler = client.getGameRoom().getGameHandler();

        String[] commandSplit = command.split(" ");

        switch (commandSplit[0]) {
            case LIST -> client.queryUserList();
            case QUEUE -> client.joinQueue();
            case MOVE -> {
                try {
                    gameHandler.handleMove(commandSplit.length == 1 ? null : commandSplit[1]);
                } catch (GameNotFoundException | GameTurnViolationException | InvalidMoveException |
                         AlgebraicNotationConversionFailed e) {
                    messageHandler.incomingMessage(SysoutHandler.ERROR + " " + e.getMessage());
                } catch (ArrayIndexOutOfBoundsException e) {
                    client.getMessageHandler().incomingMessage(SysoutHandler.UNKNOWN + " Something went wrong!");
                }
            }
            case SKIP -> {
                try {
                    gameHandler.skipTurn();
                } catch (GameNotFoundException e) {
                    messageHandler.incomingMessage(SysoutHandler.ERROR + " " + e.getMessage());
                }
            }
            case HINT -> {
                try {
                    gameHandler.giveHint();
                } catch (GameNotFoundException | GameTurnViolationException e) {
                    messageHandler.incomingMessage(SysoutHandler.ERROR + " " + e.getMessage());
                }
            }
            case HELP -> printManual();
            default -> client.getMessageHandler().incomingMessage(String.format("%s Unknown command '%s'!",
                    SysoutHandler.UNKNOWN, command));
        }
    }

    // TODO: There's a login bug, if invalid server address / port is passed at least once
    public static void main(String[] args) throws InterruptedException {
        // Initialization
        SysUtility sysUtility = new SysUtility();

        // Welcome message
        printWelcome();

        // Client creation
        Client client = createClient(sysUtility);

        // Connecting to a server
        connectClient(client, sysUtility);

        // Verifying that the automatic login process went through, otherwise retrying
        ensureLogin(client, sysUtility);

        // Printing manual
        printManual();

        // Asking for supported commands
        while (true) {
            handleCommand(client, sysUtility.readString(SysoutHandler.PROMPT + " Enter command ➨ "));

            // Waiting for the command to go through
            Thread.sleep(1000);
        }
    }
}
