package game.ai;

import game.BoardGame;
import game.OthelloGame;
import game.board.BoardMark;
import game.board.BoardMove;
import game.players.HumanPlayer;
import game.players.Player;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Random;

class AIStrategyTest {
    private static final MiniMaxCornerStrategy AI = new MiniMaxCornerStrategy();
    private BoardGame boardGame;

    @BeforeEach
    void setup() {
        this.boardGame = new OthelloGame(new HumanPlayer("AI", BoardMark.BLACK),
                new HumanPlayer("Random", BoardMark.WHITE));
    }

    @Test
    void testPerformance() {
        Random random = new Random();

        while (!this.boardGame.isGameOver()) {
            Player gameTurn = this.boardGame.getPlayerTurn();
            List<BoardMove> validMoves = this.boardGame.getValidMoves(gameTurn);

            if (validMoves.isEmpty()) {
                this.boardGame.doMove(this.boardGame.locationToMove(OthelloGame.PASSING_MOVE_INDEX));
                continue;
            }

            if (gameTurn.getUsername().equals("AI")) {
                this.boardGame.doMove(AI.determineMove(this.boardGame));
            } else {
                this.boardGame.doMove(validMoves.get(random.nextInt(validMoves.size())));
            }
        }

        int blackMarkCount = this.boardGame.getBoard().countMarks(BoardMark.BLACK);
        int whiteMarkCount = this.boardGame.getBoard().countMarks(BoardMark.WHITE);

        System.out.println("BLACK: " + blackMarkCount + " , WHITE: " + whiteMarkCount);
    }
}