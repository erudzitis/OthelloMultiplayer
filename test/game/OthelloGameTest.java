package game;

import game.board.AlgebraicNotationConversionFailed;
import game.board.BoardMark;
import game.board.BoardMove;
import game.players.HumanPlayer;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Random;

class OthelloGameTest {
    private BoardGame boardGame;

    @BeforeEach
    void setUp() {
        this.boardGame = new OthelloGame(new HumanPlayer("Ernests", BoardMark.BLACK),
                new HumanPlayer("Jonathan", BoardMark.WHITE));
    }

    /**
     * Tests if game deep copy is performed correctly and no references are left over (shallow copy)
     */
    @Test
    void testGameDeepCopy() throws AlgebraicNotationConversionFailed {
        BoardGame boardGameCopy = boardGame.deepCopy();

        // Change the original games board, copy should remain unchanged
        this.boardGame.getBoard().setField(0, BoardMark.BLACK);
        Assertions.assertEquals(BoardMark.EMPTY, boardGameCopy.getBoard().getField(0));

        // Change the original games players, copy should remain unchanged
        this.boardGame.removePlayer(this.boardGame.getPlayers().get(0));
        Assertions.assertEquals(1, this.boardGame.getPlayers().size());
        Assertions.assertEquals(2, boardGameCopy.getPlayers().size());

        // Perform a move on the original game, copy should remain unchanged
        BoardMove boardMove = this.boardGame.locationToMove(this.boardGame.getBoard().convertFromSAN("D3"));
        this.boardGame.doMove(boardMove);
        Assertions.assertTrue(this.boardGame.getBoard().countMarks(BoardMark.BLACK) >
                boardGameCopy.getBoard().countMarks(BoardMark.BLACK));
        Assertions.assertFalse(this.boardGame.getPlayerTurn().getUsername().equals(boardGameCopy.getPlayerTurn().getUsername()));
    }

    /**
     * Tests if no move object is returned (null), if an invalid move in current game turn is passed
     */
    @Test
    void testInvalidLocationToMove() {
        Assertions.assertNull(this.boardGame.locationToMove(1));
    }

    /**
     * Tests if a passing move is constructed if appropriate move location is provided (64)
     */
    @Test
    void testPassingMove() throws AlgebraicNotationConversionFailed {
        Assertions.assertTrue(this.boardGame.locationToMove(64).isPassing());
        Assertions.assertFalse(this.boardGame.locationToMove(
                this.boardGame.getBoard().convertFromSAN("D3")).isPassing());
    }

    /**
     * Tests the gameplay of a mockup game between two players
     */
    @Test
    void testMockupGame() {
        Random random = new Random();

        while (!this.boardGame.isGameOver()) {
            List<BoardMove> validMoves = this.boardGame.getValidMoves(this.boardGame.getPlayerTurn());
            // if we have any valid move to perform, we randomly choose it, otherwise we skip the turn
            BoardMove chosenMove = validMoves.isEmpty() ? this.boardGame.locationToMove(64)
                    : validMoves.get(random.nextInt(validMoves.size()));

            this.boardGame.doMove(chosenMove);

            System.out.println(this.boardGame.getBoard());
        }

        // Since in this test case no player disconnects, there is either a winner or draw depending on placed marks
        int blackMarkCount = this.boardGame.getBoard().countMarks(BoardMark.BLACK);
        int whiteMarkCount = this.boardGame.getBoard().countMarks(BoardMark.WHITE);

        System.out.println("BLACK: " + blackMarkCount);
        System.out.println("WHITE: " + whiteMarkCount);

        if (blackMarkCount > whiteMarkCount) {
            Assertions.assertTrue(this.boardGame.isWinner(this.boardGame.getPlayers().get(0)));
        } else if (blackMarkCount < whiteMarkCount) {
            Assertions.assertTrue(this.boardGame.isWinner(this.boardGame.getPlayers().get(1)));
        } else { // it's a draw
            Assertions.assertFalse(this.boardGame.isWinner(this.boardGame.getPlayers().get(0))
                    && this.boardGame.isWinner(this.boardGame.getPlayers().get(1)));
        }
    }

    /**
     * Tests if a game is immediately over if a player is disconnected
     */
    @Test
    void testMockupGameDisconnect() {
        this.boardGame.removePlayer(this.boardGame.getPlayerTurn());
        Assertions.assertTrue(this.boardGame.isGameOver());
    }
}