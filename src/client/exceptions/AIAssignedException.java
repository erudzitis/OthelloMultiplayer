package client.exceptions;

/**
 * Exception that indicates that an AI is assigned to a game room to make moves for the client
 */
public class AIAssignedException extends Exception {
    /**
     * Constructor
     */
    public AIAssignedException() {
        super("An AI is assigned to the game!");
    }
}
