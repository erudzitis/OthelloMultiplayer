package game.board;

/**
 * Exception that indicates that number conversion from or to Algebraic Notation was not successful
 */
public class AlgebraicNotationConversionFailed extends Exception {
    /**
     * Constructor
     * @param message String SAN that couldn't be converted
     */
    public AlgebraicNotationConversionFailed(String message) {
        super("Algebraic conversion failed for " + message);
    }
}
