package game.board;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

class BoardTest {
    private Board board;

    @BeforeEach
    void setUp() {
        this.board = new Board();
    }

    /**
     * Tests if the initial board state is correct. There should be 4 marks placed in the middle of the board,
     * respectively 2 BLACK and 2 WHITE.
     */
    @Test
    void testInitialState() {
        Assertions.assertFalse(board.isFull());
        Assertions.assertEquals(2, board.countMarks(BoardMark.BLACK));
        Assertions.assertEquals(2, board.countMarks(BoardMark.WHITE));
        Assertions.assertEquals(BoardMark.BLACK, board.getField(board.getIndex(4, 3)));
        Assertions.assertEquals(BoardMark.BLACK, board.getField(board.getIndex(3, 4)));
        Assertions.assertEquals(BoardMark.WHITE, board.getField(board.getIndex(3, 3)));
        Assertions.assertEquals(BoardMark.WHITE, board.getField(board.getIndex(4, 4)));

        System.out.println(board);
    }

    /**
     * Tests if the board marks value can be flipped, respectively, flipping WHITE should yield BLACK,
     * flipping BLACK should yield WHITE, however nothing should change if EMPTY is tried to be flipped.
     */
    @Test
    void testBoardMarks() {
        Assertions.assertEquals(BoardMark.BLACK, BoardMark.WHITE.getOpposite());
        Assertions.assertEquals(BoardMark.WHITE, BoardMark.BLACK.getOpposite());
        Assertions.assertEquals(BoardMark.EMPTY, BoardMark.EMPTY.getOpposite());
    }

    /**
     * Tests if Standard Algebraic Notation conversion yields correct results
     */
    @Test
    void testSANConversion() throws AlgebraicNotationConversionFailed {
        Assertions.assertEquals(0, Board.convertFromSAN("A1"));
        Assertions.assertEquals(63, Board.convertFromSAN("H8"));
        Assertions.assertEquals(19, Board.convertFromSAN("D3"));
    }

    /**
     * Tests if the method throws appropriate exception
     */
    @Test
    void testSANInvalidConversion() {
        Assertions.assertThrows(AlgebraicNotationConversionFailed.class, () -> Board.convertFromSAN("M6"));
    }

    /**
     * Tests if row, column board indexes are correctly converted to SAN
     */
    @Test
    void testToSANConversion() throws AlgebraicNotationConversionFailed {
        for (List<Integer> indexCollection: this.board.getValidMoves(BoardMark.BLACK)) {
            int location = Board.getIndex(indexCollection.get(0), indexCollection.get(1));
            String SAN = Board.convertToSAN(indexCollection.get(0), indexCollection.get(1));
            Assertions.assertEquals(location, Board.convertFromSAN(SAN));
        }
    }

    /**
     * Tests if the valid moves for each board mark get calculated correctly.
     * Initially, black mark should have 4 possible moves to perform
     */
    @Test
    void testGetValidMoves() {
        // Getting black valid moves
        List<List<Integer>> validMovesBlack = board.getValidMoves(BoardMark.BLACK);
        Assertions.assertEquals(4, validMovesBlack.size());

        // Setting black move
        List<Integer> blackMove = validMovesBlack.get(0);
        board.flipFields(blackMove.get(0),
                blackMove.get(1),
                blackMove.get(2),
                blackMove.get(3),
                blackMove.get(4),
                blackMove.get(5),
                BoardMark.BLACK);

        System.out.println(board);

        // Getting white valid moves
        List<List<Integer>> whiteValidMoves = board.getValidMoves(BoardMark.WHITE);
        Assertions.assertEquals(3, whiteValidMoves.size());
    }

    /**
     * Tests if board deep copy is performed correctly and no references are left over (shallow copy)
     */
    @Test
    void testBoardDeepCopy() {
        Board boardCopy = this.board.deepCopy();

        // Changing the first field in original board
        this.board.setField(0, BoardMark.BLACK);

        // Check if the changes have not been applied to the copied board
        Assertions.assertEquals(BoardMark.EMPTY, boardCopy.getField(0));
    }
}