package server;

import client.Client;
import game.board.BoardMark;
import helper.Await;
import networking.Protocol;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import server.handlers.ClientHandler;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.Map;
import java.util.concurrent.ExecutionException;

class ServerTest {
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
     * Tests if the server successfully starts
     */
    @Test
    void testServerStartup() {
        Assertions.assertTrue(server.isRunning());
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
}