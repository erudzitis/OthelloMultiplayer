package client.exceptions;

/**
 * Exception that indicates that a particular move on the board at the current state is not valid.
 */
public class InvalidMoveException extends Exception {
    /**
     * Constructor.
     *
     * @param message SAN notation
     */
    public InvalidMoveException(String message) {
        super("Invalid move " + message + "!");
    }
}
