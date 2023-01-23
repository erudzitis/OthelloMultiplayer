package server;

import client.Client;
import game.board.Board;
import game.board.BoardMark;
import networking.Protocol;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Arrays;

class ServerTest {
    private static Server server;
    private static boolean serverStarted = false;
    private static Client client;
    private static String RESERVED_USERNAME = "testClient";
    private static String AVAILABLE_USERNAME = "Bob";

    @BeforeEach
    void init() {
        server = new Server();
        client = new Client(RESERVED_USERNAME);
        serverStarted = server.start();
    }

    /**
     * Tests if the server successfully starts
     */
    @Test
    void testServerStartup() {
        Assertions.assertTrue(serverStarted);
    }

    /**
     * Tests if the client and server successfully establishes protocol handshake after connecting
     */
    @Test
    void testClientHandshake() throws UnknownHostException, InterruptedException {
        client.connect(InetAddress.getLocalHost(), server.getPort());

        Thread.sleep(2000);

        Assertions.assertTrue(client.isHandshakeEstablished());
    }

    /**
     * Tests if a client can login providing a unique username and is appended to the online user list
     */
    @Test
    void testClientLogin() throws UnknownHostException, InterruptedException {
        Client clientTwo = new Client(AVAILABLE_USERNAME);
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());

        Thread.sleep(2000);

        Assertions.assertTrue(server.getUserUsernames().contains(clientTwo.getUsername()));
    }

    /**
     * Tests if a client can't login when a user with the provided username has already been logged in the server,
     * can successfully login afterwards choosing a new username
     */
    @Test
    void testClientLoginExisting() throws UnknownHostException, InterruptedException {
        client.connect(InetAddress.getLocalHost(), server.getPort());
        Thread.sleep(2000);

        // Logging in when a client with provided username already exists
        Client clientTwo = new Client(RESERVED_USERNAME);
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());
        Thread.sleep(2000);

        Assertions.assertFalse(clientTwo.isSuccessfullyLoggedIn());

        // Changing client username
        clientTwo.setUsername(AVAILABLE_USERNAME);
        clientTwo.sendMessage(Protocol.loginFormat(clientTwo.getUsername()));
        Thread.sleep(2000);

        Assertions.assertTrue(clientTwo.isSuccessfullyLoggedIn());
    }

    /**
     * Tests if a client can successfully join a queue, and having joined the queue can leave the queue
     */
    @Test
    void testClientJoinLeaveQueue() throws InterruptedException, UnknownHostException {
        client.connect(InetAddress.getLocalHost(), server.getPort());
        Thread.sleep(2000);

        // Joining the queue
        client.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);

        Assertions.assertTrue(server.getQueue().contains(client.getUsername()));

        // Leaving the queue
        client.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);

        Assertions.assertFalse(server.getQueue().contains(client.getUsername()));
    }

    /**
     * Tests if server successfully creates a game room for 2 clients that join the queue
     */
    @Test
    void testServerNewGameCreation() throws UnknownHostException, InterruptedException {
        client.connect(InetAddress.getLocalHost(), server.getPort());
        Client clientTwo = new Client(AVAILABLE_USERNAME);
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());

        Thread.sleep(2000);
        client.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);
        clientTwo.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);

        Assertions.assertTrue(server.getRooms().keySet().size() == 1);
    }

    /**
     * Tests if the server successfully create a game room for 2 clients and leaves the third client waiting in the queue
     */
    @Test
    void testServerNewGameCreationPerceive() throws UnknownHostException, InterruptedException {
        client.connect(InetAddress.getLocalHost(), server.getPort());
        Client clientTwo = new Client(AVAILABLE_USERNAME);
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());
        Client clientThree = new Client("BenchWarmer");
        clientThree.connect(InetAddress.getLocalHost(), server.getPort());

        Thread.sleep(2000);
        client.sendMessage(Protocol.queueFormat());
        clientTwo.sendMessage(Protocol.queueFormat());
        clientThree.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);

        Assertions.assertTrue(server.getRooms().keySet().size() == 2);
        Assertions.assertTrue(server.getQueue().size() == 1);
    }

    /**
     * Tests if the playing a game amongst 2 clients is supported by the server
     */
    @Test
    void testServerNewGamePlay() throws UnknownHostException, InterruptedException {
        // connecting
        client.connect(InetAddress.getLocalHost(), server.getPort());
        Client clientTwo = new Client(AVAILABLE_USERNAME);
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());

        // joining queue
        Thread.sleep(2000);
        client.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);
        clientTwo.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);

        // getting reference to the match room
        GameRoom gameRoom = server.getRooms().get(server.getRooms().keySet().toArray()[0]);

        // playing game
        client.sendMessage(Protocol.moveFormat(19));
        Thread.sleep(2000);

        Assertions.assertEquals(BoardMark.BLACK, gameRoom.getGameHandler().getGame().getBoard().getField(19));
        System.out.println(gameRoom.getGameHandler().getGame().getBoard());

        // The same client should not be able to perform a move again, the game turn should have been given to opponent
        client.sendMessage(Protocol.moveFormat(20));
        Thread.sleep(2000);

        Assertions.assertEquals(BoardMark.EMPTY, gameRoom.getGameHandler().getGame().getBoard().getField(20));
        System.out.println(gameRoom.getGameHandler().getGame().getBoard());

        // The opponent should be able to perform the move
        clientTwo.sendMessage(Protocol.moveFormat(20));
        Thread.sleep(2000);

        Assertions.assertEquals(BoardMark.WHITE, gameRoom.getGameHandler().getGame().getBoard().getField(20));
        System.out.println(gameRoom.getGameHandler().getGame().getBoard());
    }

    /**
     * Tests if client disconnection while being in a game is properly handled
     */
    @Test
    void testServerGameClientDisconnect() throws UnknownHostException, InterruptedException {
        // connecting
        client.connect(InetAddress.getLocalHost(), server.getPort());
        Client clientTwo = new Client(AVAILABLE_USERNAME);
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());

        // joining queue
        Thread.sleep(2000);
        client.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);
        clientTwo.sendMessage(Protocol.queueFormat());
        Thread.sleep(2000);

        Assertions.assertTrue(server.rooms.keySet().size() == 2);

        clientTwo.sendMessage(Protocol.DISCONNECT);
        Thread.sleep(2000);

        Assertions.assertTrue(server.rooms.keySet().size() == 0);
    }
}