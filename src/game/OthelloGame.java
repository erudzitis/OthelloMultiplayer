package game;

import game.board.Board;
import game.board.BoardMark;
import game.board.BoardMove;
import game.players.Player;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class OthelloGame implements BoardGame {
    /*@public invariant gameTurn == 0 || gameTurn == 1; */

    /**
     * Holds all connected players in the game instance
     */
    private List<Player> players = new ArrayList<>();

    /**
     * Holds the index of current players turn
     */
    private /*@spec_public */ int gameTurn = 0;

    /**
     * Holds the current board associated to the game
     */
    private Board board;

    /**
     * Holds the list of allowed moves of the current game turns board mark
     */
    private List<List<Integer>> gameTurnAllowedMoves;

    /**
     * Initializes the game
     * @param p1 First Player instance
     * @param p2 Second Player instance
     */
    /*@requires p1.getMark().equals(BoardMark.BLACK);
      @requires p2.getMark().equals(BoardMark.WHITE);
      @assignable gameTurnAllowedMoves;
      @assignable players;
      @assignable board; */
    public OthelloGame(Player p1, Player p2) {
        players.add(p1);
        players.add(p2);

        this.board = new Board();
        this.gameTurnAllowedMoves = this.board.getValidMoves(BoardMark.BLACK);
    }

    /**
     * Method that checks if the particular game is over.
     * A game can be over if one of the players has disconnected / left, there's a winner or draw.
     *
     * @return true / false indicating whether the game is over
     */
    @Override
    public boolean isGameOver() {
        // TODO: Implement a way to check if any of the players have disconnected
        return false;
    }

    /**
     * Method that checks if a specific player in particular game is a winner
     *
     * @param player Player implementation
     * @return true / false
     */
    @Override
    public boolean isWinner(Player player) {
        return false;
    }

    /**
     * Method that checks if a specific player is connected to the particular game / participating
     *
     * @param player Player implementation
     * @return true / false
     */
    @Override
    public boolean playerConnected(Player player) {
        return false;
    }

    /**
     * Method that returns all connected players to the particular src.game.
     *
     * @return List<Player>, list of players
     */
    @Override
    public List<Player> getPlayers() {
        return this.players;
    }

    /**
     * Method that returns the Player of current turn
     *
     * @return Player
     */
    @Override
    public Player getPlayerTurn() {
        return this.players.get(gameTurn);
    }


    /**
     * Method that checks if the provided move is valid.
     * A provided move is valid if its current players / bots turn,
     * the field is valid field on the board and opponents marks can be outflanked.
     *
     * @param move BoardMove
     * @return true / false
     */
    @Override
    public boolean isValidMove(BoardMove move) {
        return move.getPlayer().equals(this.getPlayerTurn())
                && this.board.isField(this.board.getIndex(move.getRow(), move.getColumn()))
                && this.gameTurnAllowedMoves.contains(move.getIndexCollection());
    }

    /**
     * Method that attempts to convert index location on board to it's corresponding move object.
     * Assumes that the move is intended to be constructed for the player that has it's turn in the game
     * @param location int, location index on the board
     * @return null, if the conversion failed, otherwise BoardMove
     */
    public BoardMove locationToMove(int location) {
        // Attempt to get the corresponding move index collection
        for (List<Integer> allowedMove: this.gameTurnAllowedMoves) {
            // Provided move is in the list of current turn allowed moves
            if (this.board.getIndex(allowedMove.get(0), allowedMove.get(1)) == location) {
                // We pass the move validation forwards
                return new BoardMove(this.getPlayerTurn(), allowedMove);
            };
        }

        return null;
    }

    /**
     * Method that returns all valid moves that a player / bot could perform in this turn.
     *
     * @param player Player implementation
     * @return List<BoardMove>, list of valid moves
     */
    @Override
    public List<BoardMove> getValidMoves(Player player) {
        return this.board.getValidMoves(player.getMark()).stream()
                .map(collection -> new BoardMove(player, collection)).collect(Collectors.toList());
    }

    /**
     * Method that performs a move, respecting that the proposed move is valid
     *
     * @param move BoardMove
     */
    @Override
    public void doMove(BoardMove move) {
        // Check if move is valid
        if (!isValidMove(move)) return;

        // Perform move and flip outflanked enemy marks
        this.board.flipFields(move.getRow(),
                move.getColumn(),
                move.getSupportRow(),
                move.getSupportColumn(),
                move.getExtensionRow(),
                move.getExtensionColumn(),
                move.getPlayer().getMark());

        // Updating game turn
        this.gameTurn = (this.gameTurn + 1) % 2;

        // Updating valid moves
        this.gameTurnAllowedMoves = this.board.getValidMoves(this.getPlayerTurn().getMark());
    }

    /**
     * Method that returns the board associated to the current game
     *
     * @return
     */
    @Override
    public Board getBoard() {
        return this.board;
    }
}
