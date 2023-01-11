package game;

public interface BoardGame {
    /**
     * Method that checks if the game is over.
     * A game can be over if one of the players has disconnected / left, there's a winner or draw.
     * @return true / false indicating whether the game is over
     */
    boolean isGameOver();
}
