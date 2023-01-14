package game.board;

import java.util.Arrays;
import java.util.Collection;
import java.util.Map;

public class Board {
    /**
     * Holds the dimensions of the board
     */
    public static final int DIMENSION = 8;

    /**
     * 1D Array that holds all board fields
     */
    private BoardMark[] fields;

    /**
     * Constructor that initializes the board
     */
    /*@ assignable fields; @*/
    public Board() {
        // Initializing the board fields
        this.fields = new BoardMark[DIMENSION * DIMENSION];

        // Filling the fields with empty marks
        Arrays.fill(this.fields, BoardMark.EMPTY);

        // Initializing the default starting mark combination
        this.fields[getIndex(4, 3)] = BoardMark.BLACK;
        this.fields[getIndex(3, 4)] = BoardMark.BLACK;

        this.fields[getIndex(3, 3)] = BoardMark.WHITE;
        this.fields[getIndex(4, 4)] = BoardMark.WHITE;
    }

    /**
     * Constructor that is used for cloning the board
     * @param populatedFields BoardMark[] array
     */
    /*@ requires populatedFields.length == DIMENSION * DIMENSION;
      @ requires populatedFields[getIndex(5, 4)].equals(BoardMark.BLACK);
      @ requires populatedFields[getIndex(4, 5)].equals(BoardMark.BLACK);
      @ requires populatedFields[getIndex(4, 4)].equals(BoardMark.WHITE);
      @ requires populatedFields[getIndex(5, 5)].equals(BoardMark.WHITE);
      @ assignable fields;
      @*/
    public Board(BoardMark[] populatedFields) {
        this.fields = populatedFields;
    }

    /**
     * Method that converts the row, column pair into an index for 1D array
     * @param row
     * @param column
     * @return int, converted index, or -1, if out of bounds
     */
    /*@ requires row >= 0 && row < DIMENSION;
      @ requires column >= 0 && column < DIMENSION;
      @ pure;
      @ */
    public int getIndex(int row, int column) {
        if (!(row >= 0 && row < DIMENSION && column >= 0 && column < DIMENSION)) return -1;

        return (row * DIMENSION) + column;
    }

    /**
     * Method that indicates whether index is a valid index of a field on the board.
     * @param index int, index location on the board
     * @return true / false
     */
    /*@ ensures index >= 0 && index < DIMENSION * DIMENSION ==> \result == true;
      @ pure;
      @ */
    public boolean isField(int index) {
        return index >= 0 && index < (DIMENSION * DIMENSION);
    }

    /**
     * Method that returns the current mark of the board at a particular field.
     * @param index int, location on board
     * @return BoardMark, or null if the field is not valid
     */
    /*@ requires isField(index);
      @ ensures \result == BoardMark.EMPTY || \result == BoardMark.WHITE || \result == BoardMark.BLACK;
      @
      @ also
      @
      @ requires !isField(index);
      @ ensures \result == null;
      @*/
    public BoardMark getField(int index) {
        return !isField(index) ? null : this.fields[index];
    }

    /**
     * Method that states whether the provided field index its empty or not
     * @param index int, index location on board
     * @return true / false, false if the field doesn't exist
     */
    /*@ ensures getField(index).equals(BoardMark.EMPTY) ==> \result == true;
      @ pure;
      @*/
    public boolean isFieldEmpty(int index) {
        return getField(index).equals(BoardMark.EMPTY);
    }

    /**
     * Method that tests if the whole board is full.
     * @return true if all fields are occupied
     */
    /*@ ensures
        (\forall int i; (i >= 0 && i < DIMENSION*DIMENSION); fields[i] == BoardMark.BLACK || fields[i] == BoardMark.WHITE)
            ==> \result == true;
      @ pure;
      @*/
    public boolean isFull() {
        // Going over all mark enums in the list
        for (BoardMark mark : this.fields) {
            // If we have found an empty mark, the board is not full
            if (mark.equals(BoardMark.EMPTY)) {
                return false;
            }
        }

        return true;
    }

    /**
     * Method that computes the available valid moves for either board mark (white or black).
     * A move is valid if it outflanks the opponent marks in any row direction.
     * @return Map for each BoardMark enum type, that holds collection of row, column collection, for instance (3, 5).
     */
    public Map<BoardMark, Collection<Collection<Integer>>> getValidMoves() {
        return null;
    }


    /**
     * Method that indicates whether a particular board mark type is a winner.
     * A mark can be a winner,
     * @param mark BoardMark enum type
     * @return true / false
     */
    public boolean isWinner(BoardMark mark) {
        return false;
    }

    @Override
    public String toString() {
        String result = "";

        // Going over each row
        for (int row = 0; row < DIMENSION; row++) {
            // Going over each row fields
            for (int column = 0; column < DIMENSION; column++) {
                // Getting each field
                BoardMark storedField = fields[getIndex(row, column)];

                // If it's a new row, we add delimiter at the top and enforce a new line
                if (column == 0) {
                    result += System.lineSeparator();
                    result += "-".repeat(DIMENSION * 2 + 1);
                    result += System.lineSeparator();
                }

                // Appending formatted field to the result
                result += String.format((column == DIMENSION - 1) ? "|%s|" : "|%s", storedField.toString());
            }
        }

        return result;
    }
}
