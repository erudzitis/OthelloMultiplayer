package game.board;

import game.players.Player;

/**
 * Move holds 3 attributes, respectively the location - index on the board,
 * whose turn it is - Player,
 * and the mark of that player in the particular board game
 */
public interface Move {
    /**
     * Method that returns the Player of a particular move
     * @return Player
     */
    /*@ pure; @*/
    Player getPlayer();

    /**
     * Method that returns the location index on the board of a particular move
     * @return int, index on the board
     */
    /*@ pure; @*/
    int getLocation();

    /**
     * Method that returns the particular moves mark type
     * @return BoardMark
     */
    /*@ pure; @*/
    BoardMark getMark();
}
