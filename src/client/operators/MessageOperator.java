package client.operators;

/**
 * Interface for consuming incoming messages to be displayed for the client.
 */
public interface MessageOperator {
    /**
     * Method that consumes incoming messages
     * that should be delivered to the client and displays it accordingly,
     * supports method chaining.
     *
     * @param message String incoming message
     */
    /*@requires message != null; @*/
    MessageOperator incomingMessage(String message);
}
