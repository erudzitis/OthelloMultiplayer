package game.ai;

import game.BoardGame;
import game.board.BoardMark;
import game.board.BoardMove;
import game.players.Player;

public class ComputerPlayer extends Player {
    private static final String NAME = "SIMPLE";

    /**
     * Constructor for ComputerPlayer that also initializes its superclass
     * @param username
     * @param mark
     */
    public ComputerPlayer(String username, BoardMark mark) {
        super(String.format("%s %s", username, NAME), mark);
    }

    /**
     * Method that determines the next move (if any) for Player instance.
     * Move is determined by randomness
     *
     * @param game BoardGame, game for which to calculate the move
     * @return BoardMove
     */
    @Override
    public BoardMove determineMove(BoardGame game) {
        /*return new BoardMove(this,
                this.getMark(),
                (int) Math.random() * (game.getBoard().DIMENSION * game.getBoard().DIMENSION))*/;

       return null;
    }
}
