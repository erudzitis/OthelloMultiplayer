package game.ai;

import game.BoardGame;
import game.OthelloGame;
import game.board.BoardMark;
import game.players.Player;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.concurrent.TimeUnit;

class AIStrategyTest {
    private static final Strategy profoundAI = new MiniMaxCornerStrategy();
    private static final Strategy naiveAI = new NaiveStrategy();
    private BoardGame boardGame;

    @BeforeEach
    void setup() {
        this.boardGame = new OthelloGame(new Player("AI", BoardMark.BLACK),
                new Player("Random", BoardMark.WHITE));
    }

    /**
     * Tests more profound AI's performance against naive AI by playing 10 games against each other.
     * It is expected that profound AI wins the naive AI at least 60% of time
     */
    @Test
    void testMiniMaxCornerStrategyAgainstNaive() {
        int timesWon = 0;
        float timesPlayed = 0;

        while (timesPlayed < 10) {
            while (!this.boardGame.isGameOver()) {
                if (this.boardGame.getPlayerTurn().username().equals("AI")) {
                    this.boardGame.doMove(profoundAI.determineMove(this.boardGame));
                } else {
                    this.boardGame.doMove(naiveAI.determineMove(this.boardGame));
                }
            }

            int blackMarkCount = this.boardGame.getBoard().countMarks(BoardMark.BLACK);
            int whiteMarkCount = this.boardGame.getBoard().countMarks(BoardMark.WHITE);

            if (blackMarkCount > whiteMarkCount) timesWon++;

            setup();
            timesPlayed++;
        }

        float result = timesWon / timesPlayed;
        System.out.println(result);
        Assertions.assertTrue(result >= 0.6);
    }

    /**
     * Tests if profound AI strategy takes less than ~ 5 seconds on average to compute the next move,
     * required by the AI tournament.
     */
    @Test
    void testMiniMaxCornerStrategyComputationTime() {
        int movesComputed = 0;
        long totalTime = 0;

        while (!this.boardGame.isGameOver()) {
            if (this.boardGame.getPlayerTurn().username().equals("AI")) {
                long start = System.currentTimeMillis();

                this.boardGame.doMove(profoundAI.determineMove(this.boardGame));

                movesComputed++;
                totalTime += System.currentTimeMillis() - start;
            } else {
                this.boardGame.doMove(naiveAI.determineMove(this.boardGame));
            }
        }

        long averageTime = TimeUnit.MILLISECONDS.toSeconds(totalTime / movesComputed);

        Assertions.assertTrue(averageTime <= 5);
    }
}