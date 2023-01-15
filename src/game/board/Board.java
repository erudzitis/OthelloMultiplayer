package game.board;

import java.util.*;

public class Board {
    /**
     * Holds the dimensions of the board
     */
    public static final int DIMENSION = 8;

    /**
     * 2D Array that holds all direction extension point pairs (row, column) for a board field, respectively
     * UP, DOWN, LEFT, RIGHT,
     * UP-LEFT, UP-RIGHT, DOWN-LEFT, DOWN-RIGHT
     */
    private static final int[][] EXTENSION_PAIRS = new int[][]{
            {-1, 0}, {1, 0}, {0, -1}, {0, 1},
            {-1, -1}, {-1, 1}, {1, -1}, {1, 1}
    };

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
      @ requires populatedFields[getIndex(4, 3)].equals(BoardMark.BLACK);
      @ requires populatedFields[getIndex(3, 4)].equals(BoardMark.BLACK);
      @ requires populatedFields[getIndex(3, 3)].equals(BoardMark.WHITE);
      @ requires populatedFields[getIndex(4, 4)].equals(BoardMark.WHITE);
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
     * Method that sets specific board mark in specific position, assuming index is valid, position is empty.
     * @param index int, location on the board
     * @param mark BoardMark enum type
     * @throws IllegalArgumentException
     */
    /*@requires isField(index);
      @signals_only IllegalArgumentException;
      @assignable fields;*/
    public void setField(int index, BoardMark mark) throws IllegalArgumentException {
        // Checking if the index is valid
        if (!isField(index)) throw new IllegalArgumentException("Field with provided index is not valid!");

        this.fields[index] = mark;
    }

    /**
     * Method that sets the mark position and flips all the fields in between the starting (just set mark) and end mark
     * @param startRow int, row location of new mark
     * @param startCol int, column location of new mark
     * @param endRow int, row location of supporting mark
     * @param endColumn int, column location of supporting mark
     * @param extensionRow int, vertical extension point
     * @param extensionColumn int, horizontal extension point
     * @param mark BoardMark enum type to set
     */
    /*@requires isField(getIndex(startRow, startCol));
      @requires isField(getIndex(endRow, endColumn));
      @requires mark.equals(BoardMark.WHITE) || mark.equals(BoardMark.BLACK);
      @requires (\exists int j; j > 0 && j < EXTENSION_PAIRS.length; EXTENSION_PAIRS[j][0] == extensionRow && EXTENSION_PAIRS[j][1] == extensionColumn);
      @assignable fields;*/
    public void flipFields(int startRow, int startCol, int endRow, int endColumn, int extensionRow, int extensionColumn, BoardMark mark) {
        // Setting the target field that will complete the outflanking
        setField(getIndex(startRow, startCol), mark);

        // Going into the direction of the end mark and flipping all the marks to the opposite color
        int updatedRow = startRow + extensionRow;
        int updatedColumn = startCol + extensionColumn;

        while (!((updatedRow == endRow) && (updatedColumn == endColumn))) {
            // Flipping the field
            setField(getIndex(updatedRow, updatedColumn), mark);

            // Updating the row and column
            updatedRow += extensionRow;
            updatedColumn += extensionColumn;
        }
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
     * Method that returns all extension pairs for particular board position (any of 8 directions),
     * where there is conjoining target (opponent) board mark.
     * @param row int, row starting location index on board
     * @param column int, column starting location index on board
     * @param targetMark BoardMark enum type of opponent
     * @return true / false
     */
    /*@requires isField(getIndex(row, column));
      @requires targetMark.equals(BoardMark.WHITE) || targetMark.equals(BoardMark.BLACK);
      @ensures (\forall int i; i > 0 && i < \result.size();
        (\exists int j; j > 0 && j < EXTENSION_PAIRS.length; EXTENSION_PAIRS[j].equals(\result.get(i))));
      @pure;*/
    public List<int[]> extensionPointSupport(int row, int column, BoardMark targetMark) {
        // Initializing result storage
        List<int[]> results = new ArrayList<>();

        // Going over all extension pairs
        for (int[] extensionPoint: EXTENSION_PAIRS) {
            int extensionRow = extensionPoint[0];
            int extensionColumn = extensionPoint[1];

            // Checking if addition of current extension pair locates a position on board that holds target mark,
            // and if the field in that direction besides the target mark is in bounds of the board
            if (isField(getIndex(row + extensionRow, column + extensionColumn)) &&
                    getField(getIndex(row + extensionRow, column + extensionColumn)).equals(targetMark) &&
                    isField(getIndex(row + extensionRow * 2, column + extensionColumn * 2))) {
                // We have a candidate
                results.add(extensionPoint);
            }
        }

        return results;
    }

    /**
     * Method that checks if there is support mark already placed on the board that could outflank the opponent,
     * if so, returns the board position pair of that outflanking mark (row, column),
     * if no mark is found, null is returned.
     *
     * @param row int, row current location index on board
     * @param column int, column current location index on board
     * @param extensionRow int, extension vertically
     * @param extensionColumn int, extension horizontally
     * @param mark BoardMark enum type for who we are searching the support for
     * @return List<Integer> (row, column) pair or null
     */
    /*@requires getField(getIndex(row, column)).equals(mark);
      @ensures \result != null;
      @
      @also
      @
      @requires !isField(getIndex(row + extensionRow, column + extensionColumn));
      @ensures \result == null;*/
    public List<Integer> extensionLineSupport(int row, int column, int extensionRow, int extensionColumn, BoardMark mark) {
        // Checking if we have found the 'our' mark
        if (getField(getIndex(row, column)).equals(mark)) return new ArrayList<>(Arrays.asList(row, column));

        // We haven't found outflanking mark, we continue
        // Check if there is no empty space between
        if (isFieldEmpty(getIndex(row + extensionRow, column + extensionColumn))) return null;

        // Check if we are not going out of bounds with our next step
        if (!isField(getIndex(row + extensionRow, column + extensionColumn))) return null;

        // Otherwise, we recursively call the method until we run in either of the conditions
        return extensionLineSupport(row + extensionRow, column + extensionColumn, extensionRow, extensionColumn, mark);
    }

    /**
     * Method that computes the available valid moves for either provided board mark (white or black).
     * A move is valid if it outflanks the opponent marks in any row direction.
     *
     * @param mark BoardMark enum type for who to calculate the valid moves
     * @return List<List<Integer>> for specified BoardMark enum type,
     * that holds collection of row, column collection (valid move and it's outflank end position),
     * for instance (2, 3, 3, 4, -1, -1), where (2, 3) is valid position where to place the mark,
     * but (3, 4) is the position of supporting mark. (-1, -1) is the extension point.
     */
    /*@requires mark.equals(BoardMark.WHITE) || mark.equals(BoardMark.BLACK);
      @ensures (\forall int i; i > 0 && i < \result.size();
        isFieldEmpty(getIndex(\result.get(i).get(0), \result.get(i).get(1)))
        && !Objects.isNull(getField(getIndex(\result.get(i).get(2), \result.get(i).get(3))))
        && getField(getIndex(\result.get(i).get(2), \result.get(i).get(3))).equals(mark));
      @pure;*/
    public List<List<Integer>> getValidMoves(BoardMark mark) {
        // Initializing storage
        List<List<Integer>> results = new ArrayList<>();

        // Going over all rows
        for (int row = 0; row < DIMENSION; row++) {
            // Going over all columns of each row
            for (int column = 0; column < DIMENSION; column++) {
                // Checking if the current field is empty
                if (!isFieldEmpty(getIndex(row, column))) continue;

                // Current field is empty, we need to check in all possible directions,
                // if there is opponent mark placed
                Collection<int[]> extensions = extensionPointSupport(row, column, mark.getOpposite());

                // No surrounding opponent marks found, continuing to the next board field position
                if (extensions.size() == 0) continue;

                // We have the extension points, we want to check if there's a supporting board mark placed of our own,
                // that will lead to opponents board marks to be outflanked and captured
                for (int[] validExtension: extensions) {
                    int validExtensionRow = validExtension[0];
                    int validExtensionColumn = validExtension[1];

                    // Searching for supporting mark. Adding 2X the extension values to the search row and column,
                    // because we have checked that the position after the conjoining opponent mark is bounds of the board
                    List<Integer> support = extensionLineSupport(row + (validExtensionRow * 2),
                            column + (validExtensionColumn * 2),
                            validExtensionRow,
                            validExtensionColumn,
                            mark);

                    // We have found a valid move
                    if (!Objects.isNull(support)) {
                        int supportMarkRow = support.get(0);
                        int supportMarkColumn = support.get(1);

                        results.add(new ArrayList<>(Arrays.asList(row,
                                column,
                                supportMarkRow,
                                supportMarkColumn,
                                validExtensionRow,
                                validExtensionColumn)));
                    }
                }
            }
        }

        return results;
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
