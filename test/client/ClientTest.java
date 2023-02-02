package client;

import helper.Await;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import server.Server;

import java.io.*;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.concurrent.ExecutionException;

class ClientTest {
    private static final String USERNAME = "test";
    private static Client client;
    private static Server server;
    private static boolean isConnected = false;

    @BeforeAll
    static void init() throws UnknownHostException {
        server = new Server();
        server.start();

        client = new Client(USERNAME);
        isConnected = client.connect(InetAddress.getLocalHost(), server.getPort());
    }

    /**
     * Tests if the client can successfully connect to the server
     */
    @Test
    void testClientConnect() {
        Assertions.assertTrue(isConnected);
    }

    /**
     * Tests if the client and server successfully establishes protocol handshake after connecting
     */
    @Test
    void testClientHandshake() {
        Assertions.assertTrue(client.isHandshakeEstablished());
    }

    /**
     * Tests if a client can login providing a unique username and is appended to the online user list
     */
    @Test
    void testClientLogin() throws InterruptedException, ExecutionException {
        // Creating the client with available username and attempting to connect
        Assertions.assertTrue(new Await<Boolean>()
                .submitExpected(() -> client.isSuccessfullyLoggedIn()
                        && server.getUserUsernames().contains(client.getUsername()), true)
                .get());
    }

    /**
     * Tests if a client is not allowed to change the username / attempt to login anymore if already logged in to the server
     */
    @Test
    void testClientMoreAttemptedLogins() {
        client.attemptLogin("newUsername");
        Assertions.assertEquals(USERNAME, client.getUsername());
    }

    /**
     * Tests if client can retrieve the list of online users, where the current connected client also is expected to be
     * @throws ExecutionException
     * @throws InterruptedException
     */
    @Test
    void testGetOnlineUsers() throws ExecutionException, InterruptedException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out));

        if (client.isSuccessfullyLoggedIn()) {
            client.queryUserList();
        }

        new Await<Boolean>().delay(() -> true).get();

        Assertions.assertTrue(out.toString().contains(client.getUsername()));
    }
}