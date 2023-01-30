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
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

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

    // Client instance associated to the TUI
    private Client client;

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
     * @param sysUtility SysUtility for retrieving user input
     */
    public void connectClient(SysUtility sysUtility) {
        InetAddress serverAddress = getServerAddress(sysUtility);
        int serverPort = getServerPort(sysUtility);
        boolean connected = this.client.connect(serverAddress, serverPort);

        // If client couldn't connect to the provided server, we ask for address and port again
        if (!connected) {
            this.client.getMessageHandler().incomingMessage(SysoutHandler.ERROR + " Couldn't connect to the server!");
            Executors.newSingleThreadScheduledExecutor().schedule(() -> this.connectClient(sysUtility),
                    2000, TimeUnit.MILLISECONDS);
        } else {
            // Connected successfully, proceed to ensure that log in was a success
            Executors.newSingleThreadScheduledExecutor().schedule(() -> this.ensureLogin(sysUtility),
                    2000, TimeUnit.MILLISECONDS);
        }
    }

    /**
     * Helper method that makes sure that client's username was accepted by the server and client successfully logs in,
     * assigns the accepted username in client GameHandler
     *
     * @param sysUtility SysUtility for retrieving user input
     */
    public void ensureLogin(SysUtility sysUtility) {
        // Client is still not logged in
        if (!this.client.isSuccessfullyLoggedIn()) {
            this.client.attemptLogin(sysUtility.readString(SysoutHandler.LOCK + " Username taken, try again ➨ "));

            Executors.newSingleThreadScheduledExecutor().schedule(() -> this.ensureLogin(sysUtility),
                    2000, TimeUnit.MILLISECONDS);
        } else {
            // Logged in successfully, print the manual
            printManual();

            // Ask for supported commands
            Executors.newSingleThreadScheduledExecutor().scheduleWithFixedDelay(() -> {
                this.handleCommand(sysUtility.readString(SysoutHandler.PROMPT + " Enter command ➨ "));
            }, 0, 2000, TimeUnit.MILLISECONDS);
        }
    }

    public void handleCommand(String command) {
        MessageHandler messageHandler = this.client.getMessageHandler();
        GameHandler gameHandler = this.client.getGameRoom().getGameHandler();
        String[] commandSplit = command.split(" ");

        switch (commandSplit[0]) {
            case LIST -> this.client.queryUserList();
            case QUEUE -> this.client.joinQueue();
            case MOVE -> {
                try {
                    gameHandler.handleMove(commandSplit.length == 1 ? null : commandSplit[1]);
                } catch (GameNotFoundException | GameTurnViolationException | InvalidMoveException |
                         AlgebraicNotationConversionFailed e) {
                    messageHandler.incomingMessage(SysoutHandler.ERROR + " " + e.getMessage());
                } catch (ArrayIndexOutOfBoundsException e) {
                    messageHandler.incomingMessage(SysoutHandler.UNKNOWN + " Something went wrong!");
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
            default -> messageHandler.incomingMessage(String.format("%s Unknown command '%s'!",
                    SysoutHandler.UNKNOWN, command));
        }
    }

    public static void main(String[] args) {
        // Initialization
        SysUtility sysUtility = new SysUtility();
        ClientTUI tui = new ClientTUI();

        // Welcome message
        printWelcome();

        // Client creation
        Client client = createClient(sysUtility);
        tui.client = client;

        // Connecting to a server and verifying that the automatic login process went through
        tui.connectClient(sysUtility);
    }
}
