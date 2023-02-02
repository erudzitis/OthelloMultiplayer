package game.ai;

import game.BoardGame;
import game.board.BoardMove;

/**
 * Interface that defines methods for the strategy of computer players.
 */
public interface Strategy {
    /**
     * Method that returns the best move according to the current Strategy.
     *
     * @param game current game
     * @return the best move according to the strategy
     */
    public BoardMove determineMove(BoardGame game);
}
