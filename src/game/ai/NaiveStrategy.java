package game.ai;

import game.BoardGame;
import game.board.BoardMove;

import java.util.List;
import java.util.Random;

/**
 * Strategy that is based on randomness.
 */
public class NaiveStrategy implements Strategy {
    /**
     * Re-usable PRNG.
     */
    private static final Random RANDOM = new Random();

    /**
     * Method that returns the best move according to the current Strategy.
     *
     * @param game current game
     * @return the best move according to the strategy
     */
    @Override
    public BoardMove determineMove(BoardGame game) {
        List<BoardMove> validMoves = game.getValidMoves(game.getPlayerTurn());

        return validMoves.isEmpty()
                ? game.passingMove() : validMoves.get(RANDOM.nextInt(validMoves.size()));
    }
}
