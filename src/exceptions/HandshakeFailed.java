package exceptions;

public class HandshakeFailed extends Exception {
    public HandshakeFailed(String message) {
        super(message);
    }

    public HandshakeFailed() {
        super("HELLO protocol message expected");
    }
}
