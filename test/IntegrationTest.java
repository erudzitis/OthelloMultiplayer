
import client.Client;
import game.board.BoardMark;
import helper.Await;
import networking.Protocol;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import server.GameRoom;
import server.Server;
import server.handlers.ClientHandler;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Map;
import java.util.concurrent.ExecutionException;

class IntegrationTest {
    private static Server server;
    private static Client clientOne;
    private static Client clientTwo;
    private static final String RESERVED_USERNAME = "testClient";
    private static final String RESERVED_USERNAME_2 = "testClient2";
    private static final String AVAILABLE_USERNAME = "BenchWarmer";

    @BeforeAll
    static void init() throws UnknownHostException {
        server = new Server();
        server.start();

        testClientConnect();
    }

    static void testClientConnect() throws UnknownHostException {
        clientOne = new Client(RESERVED_USERNAME);
        clientTwo = new Client(RESERVED_USERNAME_2);

        clientOne.connect(InetAddress.getLocalHost(), server.getPort());
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());
    }

    static void cleanup() throws ExecutionException, InterruptedException, UnknownHostException {
        clientOne.sendMessage(Protocol.DISCONNECT);
        clientTwo.sendMessage(Protocol.DISCONNECT);

        new Await<Boolean>().delay(() -> true).get();

        testClientConnect();
    }


    /**
     * Tests if a client can't login when a user with the provided username has already been logged in the server,
     * can successfully login afterwards choosing a new username
     */
    @Test
    void testClientLoginExisting() throws UnknownHostException, InterruptedException, ExecutionException {
        // Logging in when a client with provided username already exists
        Client clientThree = new Client(RESERVED_USERNAME);
        clientThree.connect(InetAddress.getLocalHost(), server.getPort());

        Assertions.assertFalse(new Await<Boolean>()
                .submitExpected(clientThree::isSuccessfullyLoggedIn, false).get());

        // Changing client username
        clientThree.setUsername(AVAILABLE_USERNAME);
        clientThree.sendMessage(Protocol.loginFormat(clientThree.getUsername()));

        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(clientThree::isSuccessfullyLoggedIn, true).get());

        // Disconnecting the client so that it doesn't block further tests
        clientThree.sendMessage(Protocol.DISCONNECT);
    }

    /**
     * Tests if an online person can be added to the queue and removed
     */
    @Test
    void testAddQueue() {
        String onlineClientUsername = server.getUserUsernames().get(0);
        ClientHandler onlineClientHandler = server.getClientHandlersReverse().get(onlineClientUsername);

        server.setQueue(onlineClientHandler);

        Assertions.assertTrue(server.getQueue().contains(onlineClientUsername));

        server.setQueue(onlineClientHandler);

        Assertions.assertFalse(server.getQueue().contains(onlineClientUsername));
    }

    /**
     * Tests if a client can successfully join a queue, and having joined the queue can leave the queue
     */
    @Test
    void testClientJoinLeaveQueue() throws InterruptedException, ExecutionException {
        // Joining the queue
        clientOne.joinQueue();

        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(() -> server.getQueue().contains(clientOne.getUsername()), true).get());

        // Leaving the queue
        new Await<Boolean>().delay(() -> {
            clientOne.joinQueue();
            return true;
        }).get();

        Assertions.assertFalse(new Await<Boolean>()
                .submitExpected(() -> server.getQueue().contains(clientOne.getUsername()), false).get());
    }

    /**
     * Tests if server successfully creates a game room for 2 clients that join the queue
     */
    @Test
    void testServerNewGameCreation() throws InterruptedException, ExecutionException, UnknownHostException {
        // Joining the queue
        new Await<Boolean>().delay(() -> {
            clientOne.joinQueue();
            clientTwo.joinQueue();

            return true;
        }).get();

        System.out.println(server.getRooms().keySet());

        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(() -> server.getRooms().keySet().size() == 2, true).get());

        // Disconnecting the client so that it doesn't block further tests
        cleanup();
    }

    /**
     * Tests if the server successfully create a game room for 2 clients and leaves the third client waiting in the queue
     */
    @Test
    void testServerNewGameCreationPerceive() throws UnknownHostException, InterruptedException, ExecutionException {
        // Creating two additional clients
        Client clientThree = new Client(AVAILABLE_USERNAME);
        clientThree.connect(InetAddress.getLocalHost(), server.getPort());

        // Joining the queue
        new Await<Boolean>().delay(() -> {
            clientOne.joinQueue();
            clientTwo.joinQueue();
            clientThree.sendMessage(Protocol.queueFormat());

            return true;
        }).get();

        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(() -> server.getRooms().keySet().size() == 2, true).get());
        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(() -> server.getQueue().size() == 1, true).get());

        // Clean up
        clientThree.sendMessage(Protocol.DISCONNECT);
        cleanup();
    }

    /**
     * Tests if the playing a game amongst 2 clients is supported by the server
     */
    @Test
    void testServerNewGamePlay() throws UnknownHostException, InterruptedException, ExecutionException {
        // joining queue
        new Await<Boolean>().delay(() -> {
            clientOne.joinQueue();
            return true;
        }).get();

        new Await<Boolean>().delay(() -> {
            clientTwo.joinQueue();
            return true;
        }).get();

        new Await<Boolean>().delay(() -> true).get();

        // getting reference to the match room
        Map<ClientHandler, GameRoom> rooms = server.getRooms();
        GameRoom gameRoom = rooms.get(rooms.keySet().toArray()[0]);

        // playing game
        new Await<Boolean>().delay(() -> {
            clientOne.attemptMove(19);
            return true;
        }).get();

        Assertions.assertEquals(BoardMark.BLACK, new Await<BoardMark>()
                .submitExpected(() -> gameRoom.getGameHandler().getGame().getBoard().getField(19), BoardMark.BLACK)
                .get());

        System.out.println(gameRoom.getGameHandler().getGame().getBoard());

        // The same client should not be able to perform a move again, the game turn should have been given to opponent
        clientOne.attemptMove(20);

        Assertions.assertEquals(BoardMark.EMPTY, new Await<BoardMark>()
                .submitExpected(() -> gameRoom.getGameHandler().getGame().getBoard().getField(20), BoardMark.EMPTY)
                .get());

        System.out.println(gameRoom.getGameHandler().getGame().getBoard());

        // The opponent should be able to perform the move
        clientTwo.attemptMove(20);

        Assertions.assertEquals(BoardMark.WHITE, new Await<BoardMark>()
                .submitExpected(() -> gameRoom.getGameHandler().getGame().getBoard().getField(20), BoardMark.WHITE)
                .get());

        System.out.println(gameRoom.getGameHandler().getGame().getBoard());

        // Re-setting the state
        cleanup();
    }

    /**
     * Tests if client disconnection while being in a game is properly handled
     */
    @Test
    void testServerGameClientDisconnect() throws UnknownHostException, InterruptedException, ExecutionException {
        // joining queue
        new Await<Boolean>().delay(() -> {
            clientOne.joinQueue();
            clientTwo.joinQueue();
            return true;
        }).get();

        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(() -> server.getRooms().keySet().size() == 2, true).get());

        clientTwo.sendMessage(Protocol.DISCONNECT);

        new Await<Boolean>().delay(() -> true).get();

        System.out.println(server.getRooms().keySet());

        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(() -> server.getRooms().keySet().size() < 2, true).get());

        // Clean up
    }
}