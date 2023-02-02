package game.board;

public enum BoardMark {
    WHITE("⚪"), BLACK("⚫"), EMPTY(" ");

    /**
     * Private String that holds each enums constants value.
     */
    private final String markString;

    /**
     * Private constructor for each enum constant.
     *
     * @param markString String enum value
     */
    private BoardMark(String markString) {
        this.markString = markString;
    }

    /**
     * Holds all values (WHITE, BLACK, EMPTY).
     */
    private static final BoardMark[] VALUES = values();

    /**
     * Has to be called on a particular color board mark,
     * either WHITE or BLACK, to get the opposite one.
     * @return the next BoardMark.
     */
    /*@ ensures WHITE.getOpposite().equals(BLACK);
      @ ensures BLACK.getOpposite().equals(WHITE);
      @ ensures EMPTY.getOpposite().equals(EMPTY);
      @ pure;*/
    public BoardMark getOpposite() {
        if (this.equals(EMPTY)) {
            return EMPTY;
        }

        return VALUES[(this.ordinal() + 1) % 2];
    }

    /**
     * Returns the String representation of each enum constant.
     *
     * @return String enum representation
     */
    @Override
    public String toString() {
        return this.markString;
    }
}
