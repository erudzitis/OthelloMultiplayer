package server;

import client.Client;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;

class ServerTest {
    private static Server server;
    private static boolean serverStarted = false;
    private static Client client;

    @BeforeEach
    void init() {
        server = new Server();
        client = new Client("testClient");
        serverStarted = server.start();
    }

    /**
     * Tests if the server successfully starts
     */
    @Test
    void testServerStartup() {
        Assertions.assertTrue(serverStarted);
    }

    @Test
    void testClientHandshake() throws UnknownHostException, InterruptedException {
        client.connect(InetAddress.getLocalHost(), server.getPort());

        Thread.sleep(2000);

        Assertions.assertTrue(client.isHandshakeEstablished());
    }

    @Test
    void testClientLogin() throws UnknownHostException, InterruptedException {
        Client clientTwo = new Client("Bob");
        clientTwo.connect(InetAddress.getLocalHost(), server.getPort());

        Thread.sleep(2000);

        Assertions.assertTrue(server.getUserUsernames().contains(clientTwo.getUsername()));
    }
}