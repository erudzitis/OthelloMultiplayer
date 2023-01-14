package game.board;

import src.game.players.Player;

public class BoardMove {
    private Player player;
    private BoardMark mark;
    private int location;

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
    public Player getPlayer() {
        return this.player;
    }

    /**
     * Method that returns the location index on the board of a particular move
     * @return int, index on the board
     */
    public int getLocation() {
        return this.location;
    }

    /**
     * Method that returns the particular moves mark type
     * @return BoardMark
     */
    public BoardMark getMark() {
        return this.mark;
    }
}
