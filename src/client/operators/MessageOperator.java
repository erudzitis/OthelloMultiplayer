package client.operators;

public interface MessageOperator {
    /**
     * Method that consumes incoming messages that should be delivered to the client and displays it accordingly,
     * supports method chaining
     *
     * @param message String incoming message
     */
    MessageOperator incomingMessage(String message);
}
