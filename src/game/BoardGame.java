package game;

import game.board.BoardMove;
import src.game.players.Player;
import java.util.List;

public interface BoardGame {
    /*@ public invariant getPlayers().size() > 0 && getPlayers().size() <= 2; @*/

    /**
     * Method that checks if the particular src.game is over.
     * A src.game can be over if one of the players has disconnected / left, there's a winner or draw.
     * @return true / false indicating whether the src.game is over
     */
    /*@ pure; @*/
    boolean isGameOver();

    /**
     * Method that checks if a specific player in particular src.game is a winner
     * @param player Player implementation
     * @return true / false
     */
    /*@ requires playerConnected(player);
      @ pure;
      @*/
    boolean isWinner(Player player);

    /**
     * Method that checks if a specific player is connected to the particular src.game / participating
     * @param player Player implementation
     * @return true / false
     */
    /*@ pure; @*/
    boolean playerConnected(Player player);

    /**
     * Method that returns all connected players to the particular src.game.
     * @return List<Player>, list of players
     */
    /*@ pure; @*/
    List<Player> getPlayers();

    /**
     * Method that checks if the provided move is valid.
     * A provided move is valid if its current players / bots turn, the field is valid field on the board and not occupied
     * @param move BoardMove
     * @return
     */
    /*@ pure; @*/
    boolean isValidMove(BoardMove move);

    /**
     * Method that returns all valid moves that a player / bot could perform in this turn.
     * A move counts valid if the particular field is not occupied and moving to the field would outflank your opponent.
     * @param player Player implementation
     * @return List<BoardMove>, list of valid moves
     */
    /*@ ensures (\forall int i; i >= 0 & i < \result.size(); isValidMove(\result.get(i)));
      @ pure;
      @*/
    List<BoardMove> getValidMoves(Player player);

    /**
     * Method that performs a move, respecting that the proposed move is valid
     * @param move BoardMove
     */
    /*@ requires isValidMove(move); @*/
    void doMove(BoardMove move);
}
