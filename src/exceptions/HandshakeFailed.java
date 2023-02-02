package exceptions;

/**
 * Exception that indicates that the handshake between client / server has not been established.
 */
public class HandshakeFailed extends Exception {
    /**
     * Constructor with custom exception message.
     *
     * @param message String exception message
     */
    public HandshakeFailed(String message) {
        super(message);
    }

    /**
     * Constructor.
     */
    public HandshakeFailed() {
        this("HELLO protocol message expected");
    }
}
