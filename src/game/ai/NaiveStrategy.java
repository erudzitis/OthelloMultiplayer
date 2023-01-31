package game.ai;

import game.BoardGame;
import game.OthelloGame;
import game.board.BoardMove;

import java.util.List;
import java.util.Random;

/**
 * Strategy that is based on randomness
 */
public class NaiveStrategy implements Strategy {
    /**
     * Re-usable PRNG
     */
    private static final Random random = new Random();

    /**
     * Method that returns the best move according to the current Strategy
     *
     * @param game current game
     * @return the best move according to the strategy
     */
    @Override
    public BoardMove determineMove(BoardGame game) {
        List<BoardMove> validMoves = game.getValidMoves(game.getPlayerTurn());

        return validMoves.isEmpty()
                ? game.locationToMove(OthelloGame.PASSING_MOVE_INDEX)
                : validMoves.get(random.nextInt(validMoves.size()));
    }
}
