package game.board;

public class AlgebraicNotationConversionFailed extends Exception {
    public AlgebraicNotationConversionFailed(String message) {
        super("Algebraic conversion failed for " + message);
    }
}
