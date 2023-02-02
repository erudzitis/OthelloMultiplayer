package game.players;

import game.board.BoardMark;

/**
 * Record for Player.
 *
 * @param username String player username
 * @param mark BoardMark assigned to the player
 */
public record Player(String username, BoardMark mark) {
    /**
     * Constructor used for cloning purposes.
     *
     * @param player Player instance to perform copy on
     */
    public Player(Player player) {
        this(player.username, player.mark);
    }
}
