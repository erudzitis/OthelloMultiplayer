package client.exceptions;

/**
 * Exception that indicates that a game command has been attempted while its opponents turn.
 */
public class GameTurnViolationException extends Exception {
    /**
     * Constructor.
     */
    public GameTurnViolationException() {
        super("It's not your game turn!");
    }
}
