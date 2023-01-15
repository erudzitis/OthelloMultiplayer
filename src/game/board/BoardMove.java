package game.board;

import src.game.players.Player;

public class BoardMove {
    private Player player;
    private /*@spec_public;*/ BoardMark mark;
    private /*@spec_public;*/ int location;

    /*@public invariant mark.equals(BoardMark.WHITE) || mark.equals(BoardMark.BLACK);
      @public invariant location >= 0 && location < (Board.DIMENSION * Board.DIMENSION);*/

    /**
     * Constructor that initializes the object
     * @param player Player implementation
     * @param mark BoardMark enum type
     * @param location int, index of the location on the board
     */
    public BoardMove(Player player, BoardMark mark, int location) {
        this.player = player;
        this.mark = mark;
        this.location = location;
    }

    /**
     * Method that returns the Player of a particular move
     * @return Player
     */
    /*@pure; @*/
    public Player getPlayer() {
        return this.player;
    }

    /**
     * Method that returns the location index on the board of a particular move
     * @return int, index on the board
     */
    /*@pure; @*/
    public int getLocation() {
        return this.location;
    }

    /**
     * Method that returns the particular moves mark type
     * @return BoardMark
     */
    /*@pure; @*/
    public BoardMark getMark() {
        return this.mark;
    }
}
