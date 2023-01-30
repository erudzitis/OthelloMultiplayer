package client.handlers;

public interface MessageHandler {
    /**
     * Method that consumes incoming messages that should be delivered to the client and displays it accordingly,
     * supports method chaining
     *
     * @param message String incoming message
     */
    MessageHandler incomingMessage(String message);
}
