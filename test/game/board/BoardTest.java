package game.board;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

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
        Assertions.assertEquals(board.getField(board.getIndex(4, 3)), BoardMark.BLACK);
        Assertions.assertEquals(board.getField(board.getIndex(3, 4)), BoardMark.BLACK);
        Assertions.assertEquals(board.getField(board.getIndex(3, 3)), BoardMark.WHITE);
        Assertions.assertEquals(board.getField(board.getIndex(4, 4)), BoardMark.WHITE);

        System.out.println(board);
    }

    /**
     * Tests if the board marks value can be flipped, respectively, flipping WHITE should yield BLACK,
     * flipping BLACK should yield WHITE, however nothing should change if EMPTY is tried to be flipped.
     */
    @Test
    void testBoardMarks() {
        Assertions.assertEquals(BoardMark.WHITE.getOpposite(), BoardMark.BLACK);
        Assertions.assertEquals(BoardMark.BLACK.getOpposite(), BoardMark.WHITE);
        Assertions.assertEquals(BoardMark.EMPTY.getOpposite(), BoardMark.EMPTY);
    }
}