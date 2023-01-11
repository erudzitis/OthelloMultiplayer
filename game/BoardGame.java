package game;

import game.board.BoardMark;
import game.board.BoardMove;
import game.board.Move;
import game.players.Player;

import java.util.List;

public interface BoardGame {
    /*@ public invariant getPlayers().size() > 0 && getPlayers().size() <= 2; @*/

    /**
     * Method that checks if the particular game is over.
     * A game can be over if one of the players has disconnected / left, there's a winner or draw.
     * @return true / false indicating whether the game is over
     */
    /*@ pure; @*/
    boolean isGameOver();

    /**
     * Method that checks if a specific board mark type has defeated the other in a particular game
     * @param mark BoardMark enum type
     * @return true / false
     */
    /*@ pure; @*/
    boolean isWinner(BoardMark mark);

    /**
     * Method that checks if a specific player in particular game is a winner
     * @param player Player implementation
     * @return true / false
     */
    /*@ requires playerConnected(player);
      @ pure;
      @*/
    boolean isWinner(Player player);

    /**
     * Method that checks if a specific player is connected to the particular game / participating
     * @param player Player implementation
     * @return true / false
     */
    /*@ pure; @*/
    boolean playerConnected(Player player);

    /**
     * Method that returns all connected players to the particular game.
     * @return List<Player>, list of players
     */
    /*@ spec_public;
      @ pure;
      @*/
    List<Player> getPlayers();

    /**
     * Method that checks if the provided move is valid.
     * A provided move is valid if its current players / bots turn, the field is valid field on the board and not occupied
     * @param move Move implementation
     * @return
     */
    /*@ pure; @*/
    boolean isValidMove(Move move);

    /**
     * Method that returns all valid moves that a player / bot could perform in this turn.
     * A move counts valid if the particular field is not occupied.
     * @return List<Move>, list of valid moves
     */
    /*@ ensures (\forall int i; i >= 0 & i < \result.size(); isValidMove(\result.get(i)));
      @ pure;
      @*/
    List<Move> getValidMoves();

    /**
     * Method that performs a move, respecting that the proposed move is valid
     * @param move Move implementation
     */
    /*@ requires isValidMove(move); @*/
    void doMove(Move move);
}
