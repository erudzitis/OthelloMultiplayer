package server;

import client.Client;
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
}