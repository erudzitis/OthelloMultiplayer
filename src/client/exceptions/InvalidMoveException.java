package client.exceptions;

import game.board.BoardMove;

/**
 * Exception that indicates that a particular move on the board at the current state is not valid
 */
public class InvalidMoveException extends Exception {
    /**
     * Constructor
     *
     * @param move BoardMove instance or null
     */
    public InvalidMoveException(BoardMove move) {
        super(move == null ? "Invalid move" :
                String.format("Invalid move row: %s, column: %s!", move.getRow(), move.getColumn()));
    }
}
