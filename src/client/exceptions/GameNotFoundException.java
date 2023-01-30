package client.exceptions;

/**
 * Exception that indicates that there is no ongoing game at the moment
 */
public class GameNotFoundException extends Exception {
    /**
     * Constructor
     */
    public GameNotFoundException() {
        super("There is no ongoing game found!");
    }
}
