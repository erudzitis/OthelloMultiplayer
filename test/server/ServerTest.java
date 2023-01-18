package server;

import client.Client;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.net.InetAddress;
import java.net.UnknownHostException;

class ServerTest {
    private static Server server;

    @BeforeAll
    public static void init() {
        server = new Server();
    }

    /**
     * Tests if the server successfully starts
     */
    @Test
    void testServerStartup() {
        boolean serverStarted = server.start();

        Assertions.assertTrue(serverStarted);
    }

    @Test
    void testClientConnection() throws UnknownHostException, InterruptedException {
        server.start();

        Client client = new Client("testClient");
        client.connect(InetAddress.getLocalHost(), server.getPort());

        Thread.sleep(2000);

        Assertions.assertTrue(client.isHandshakeEstablished());
    }
}