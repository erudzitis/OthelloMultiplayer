package game.players;

import game.BoardGame;
import game.board.BoardMark;
import game.board.BoardMove;

public abstract class Player {
    private String username;
    private BoardMark mark;

    public Player(String username, BoardMark mark) {
        this.username = username;
        this.mark = mark;
    }

    /**
     * Constructor used for deep copy purposes
     * @param player Player original instance
     */
    public Player(Player player) {
        this.username = player.username;
        this.mark = player.mark;
    }

    /**
     * Getter for player username
     * @return String, name of the player
     */
    /*@pure; @*/
    public String getUsername() {
        return this.username;
    }

    /**
     * Getter for assigned player mark
     * @return BoardMark enum type
     */
    /*@pure; @*/
    public BoardMark getMark() {
        return this.mark;
    }

    /**
     * Setter for assigning a new mark to the player
     * @param mark BoardMark enum type
     */
    /*@requires mark.equals(BoardMark.WHITE) || mark.equals(BoardMark.BLACK);
      @assignable mark;*/
    public void setMark(BoardMark mark) {
        this.mark = mark;
    }

    /**
     * Method that determines the next move (if any) for Player instance
     * @param game BoardGame, game for which to calculate the move
     * @return BoardMove
     */
    /*@requires game != null;
      @ensures \result.getLocation() >= 0 && \result.getLocation() < (game.getBoard().DIMENSION * game.getBoard().DIMENSION);
      @pure;*/
    public abstract BoardMove determineMove(BoardGame game);
}
