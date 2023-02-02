package game.ai;

import game.BoardGame;
import game.board.Board;
import game.board.BoardMark;
import game.board.BoardMove;

import java.util.*;

/**
 * Minimax algorithm, going for corners.
 */
public class MiniMaxCornerStrategy implements Strategy {
    //test depth
    private static final int MAX_DEPTH = 4;

    private static final List<Integer> VALUE_4 = Arrays.asList(0, 7, 63, 56);
    private static final List<Integer> VALUE_NEG_3 = Arrays.asList(1, 6, 8, 15, 48, 55, 57, 62);
    private static final List<Integer> VALUE_NEG_4 = Arrays.asList(9, 14, 49, 54);
    private static final List<Integer> VALUE_2 = Arrays.asList(2, 3, 4, 5, 16, 24, 32, 40, 23,
        31, 39, 47, 58, 59, 60, 61);
    private static final List<Integer> VALUE_NEG_1 = Arrays.asList(10, 11, 12, 13, 17, 25,
        33, 41, 22, 30, 38, 46, 50, 51, 52, 53);
    private static final List<Integer> VALUE_1 = Arrays.asList(27, 28, 35, 36, 18, 21, 42, 45);
    private static final Map<Integer, List<Integer>> VALUES = Map.ofEntries(
            Map.entry(4, VALUE_4),
            Map.entry(-3, VALUE_NEG_3),
            Map.entry(-4, VALUE_NEG_4),
            Map.entry(2, VALUE_2),
            Map.entry(-1, VALUE_NEG_1),
            Map.entry(1, VALUE_1)
    );

    @Override
    public BoardMove determineMove(BoardGame game) {
        //initial best score
        int bestScore = -10000;
        BoardMove bestMove = null;

        //pass move if no move available
        if (game.getValidMoves(game.getPlayerTurn()).isEmpty()) {
            return game.passingMove();
        }

        for (BoardMove move : game.getValidMoves(game.getPlayerTurn())) {
            //create a copy for each move and change the state
            // of that copy to a state with the move done
            BoardGame gameCopy = game.deepCopy();
            gameCopy.doMove(move);

            //check the score of the move according to maxmin and getScore
            int score = minMaxValue(gameCopy, 0, false);

            //keep track of highest score
            if (score > bestScore) {
                bestScore = score;
                bestMove = move;
            }

        }

        return bestMove;
    }

    /**
     * @param game current state of the game
     * @return int the score according to mark count and weights
     */
    public int getScore(BoardGame game) {
        Board board = game.getBoard();
        BoardMark gameTurnMark = game.getPlayerTurn().mark();
        BoardMark oppositeMark = gameTurnMark.getOpposite();

        int score = 0;

        for (Map.Entry<Integer, List<Integer>> valueEntry: VALUES.entrySet()) {
            int baseValue = valueEntry.getKey();

            for (int fieldLocation: valueEntry.getValue()) {
                if (board.getField(fieldLocation).equals(gameTurnMark)) {
                    score += baseValue;
                } else if (board.getField(fieldLocation).equals(oppositeMark)) {
                    score += baseValue * (-1);
                }
            }
        }

        return score;
    }

    /**
     * @param game  the gamestate that should be evaluated
     * @param depth how far the algorithm should go
     * @param isMax checks if the current turn is a max(own) or min(opponent) turn
     * @return the score which is evaluated using maxmin algorithm and getScore evaluation
     */
    public int minMaxValue(BoardGame game, int depth, boolean isMax) {

        //checks if depth of certain value is reached or the game is over
        if (depth == MAX_DEPTH || game.isGameOver()) {
            return getScore(game);
        } else {
            List<Integer> scores = new ArrayList<>();
            for (BoardMove move : game.getValidMoves(game.getPlayerTurn())) {
                //create a copy for each move and do the move on the copy
                BoardGame currentCopy = game.deepCopy();
                currentCopy.doMove(move);

                // recurs call on minmax advancing the depth and switching between min and max
                //either receive the max/min element of scores or the score of a end node
                int score = minMaxValue(currentCopy, depth + 1, !isMax);
                scores.add(score);
            }

            if (scores.isEmpty()) {
                return 0;
            }

            //check if the current depth is max or min
            if (isMax) {
                return Collections.max(scores);
            } else {
                return Collections.min(scores);
            }
        }

    }


}

