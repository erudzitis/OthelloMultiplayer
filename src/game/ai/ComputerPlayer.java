package game.ai;

import game.BoardGame;
import game.board.BoardMove;

/**
 * Record for ComputerPlayer.
 *
 * @param strategy Strategy attached to the instance
 */
public record ComputerPlayer(Strategy strategy) {
    /**
     * Method that retrieves determined move from the particular AI strategy
     * for current board game and its state.
     *
     * @param boardGame BoardGame instance to find the move for
     * @return BoardMove
     */
    public BoardMove determineMove(BoardGame boardGame) {
        return this.strategy.determineMove(boardGame);
    }
}
