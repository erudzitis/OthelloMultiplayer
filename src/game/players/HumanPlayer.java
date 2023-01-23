package game.players;

import game.BoardGame;
import game.board.BoardMark;
import game.board.BoardMove;

public class HumanPlayer extends Player {
    /**
     * Constructor for HumanPlayer that also initializes its superclass
     * @param username
     * @param mark
     */
    public HumanPlayer(String username, BoardMark mark) {
        super(username, mark);
    }
    /**
     * Constructor used for deep copy purposes
     * @param player Player original instance
     */
    public HumanPlayer(Player player) {
        super(player);
    }


    /**
     * Method that determines the next move (if any) for Player instance.
     *
     * @param game BoardGame, game for which to calculate the move
     * @return BoardMove
     */
    @Override
    public BoardMove determineMove(BoardGame game) {
        return null;
    }
}
