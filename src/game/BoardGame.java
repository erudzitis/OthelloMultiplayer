package game;

import game.board.Board;
import game.board.BoardMove;
import game.players.Player;
import java.util.List;

public interface BoardGame {
    /*@ public invariant getPlayers().size() > 0 && getPlayers().size() <= 2; @*/

    /**
     * Method that checks if the particular ame is over.
     * A game can be over if one of the players has disconnected / left, there's a winner or draw.
     * @return true / false indicating whether the game is over
     */
    /*@ pure; @*/
    boolean isGameOver();

    /**
     * Method that checks if a specific player in particular game is a winner
     * @param player Player implementation
     * @return true / false
     */
    /*@ requires isPlayerConnected(player);
      @ pure;
      @*/
    boolean isWinner(Player player);

    /**
     * Method that attempts to retrieve the winner of the game, assuming the game is over.
     *
     * @return null, if it's a draw, Player the winner otherwise
     */
    Player getWinner();

    /**
     * Method that checks if a specific player is connected to the particular game.
     *
     * @param player Player implementation
     * @return true / false
     */
    /*@ pure; @*/
    boolean isPlayerConnected(Player player);

    /**
     * Method that removes player from the list of players.
     *
     * @param player Player instance
     */
    void removePlayer(Player player);

    /**
     * Method that returns all connected players to the particular game.
     *
     * @return List<Player>, list of players
     */
    /*@ pure; @*/
    List<Player> getPlayers();

    /**
     * Method that returns the Player of current turn.
     *
     * @return Player
     */
    Player getPlayerTurn();

    /**
     * Method that checks if the provided move is valid.
     * A provided move is valid if its current players / bots turn,
     * the field is valid field on the board and opponents marks can be outflanked.
     * @param move BoardMove
     * @return true / false
     */
    /*@ pure; @*/
    boolean isValidMove(BoardMove move);

    /**
     * Method that attempts to convert index location on board to it's corresponding move object
     * Assumes that the move is intended to be constructed for the player
     * that has its turn in the game.
     *
     * @param location int, location index on the board
     * @return null, if the conversion failed, otherwise BoardMove
     */
    BoardMove locationToMove(int location);

    /**
     * Method that returns a passing move.
     *
     * @return BoardMove that is passing
     */
    BoardMove passingMove();

    /**
     * Method that returns all valid moves that a player / bot could perform in this turn.
     * @param player Player implementation
     * @return List<BoardMove>, list of valid moves
     */
    /*@ ensures (\forall int i; i >= 0 & i < \result.size(); isValidMove(\result.get(i)));
      @ pure;
      @*/
    List<BoardMove> getValidMoves(Player player);

    /**
     * Method that performs a move and its outflanks, respecting that the proposed move is valid.
     *
     * @param move BoardMove
     */
    /*@ requires isValidMove(move); @*/
    void doMove(BoardMove move);

    /**
     * Method that returns the board associated to the current game.
     *
     * @return Board
     */
    Board getBoard();

    /**
     * Method that returns the deep copy of current games state.
     *
     * @return Deep copied BoardGame instance
     */
    BoardGame deepCopy();
}
