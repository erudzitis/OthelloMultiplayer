package game;

import game.board.Board;
import game.board.BoardMark;
import game.board.BoardMove;
import game.players.Player;

import java.util.ArrayList;
import java.util.List;

/**
 * Othello's implementation of the board game
 */
public class OthelloGame implements BoardGame {
    /*@public invariant gameTurn == 0 || gameTurn == 1; */

    /**
     * Holds the index that indicates that the move should be a passing move
     */
    public static final int PASSING_MOVE_INDEX = 64;

    /**
     * Holds list of all connected player objects in the game instance
     */
    private final List<Player> players = new ArrayList<>();

    /**
     * Holds the index of current players turn
     */
    private /*@spec_public */ int gameTurn = 0;

    /**
     * Holds the current board associated to the game
     */
    private Board board;

    /**
     * Holds the list of allowed moves of the current game turns board mark, for performance / internal access reasons
     */
    private List<List<Integer>> gameTurnAllowedMoves;

    /**
     * Initializes the game
     *
     * @param p1 First Player instance
     * @param p2 Second Player instance
     */
    /*@requires p1.mark().equals(BoardMark.BLACK);
      @requires p2.mark().equals(BoardMark.WHITE);
      @assignable gameTurnAllowedMoves;
      @assignable board; */
    public OthelloGame(Player p1, Player p2) {
        this.players.add(p1);
        this.players.add(p2);

        this.board = new Board();
        this.gameTurnAllowedMoves = this.board.getValidMoves(BoardMark.BLACK);
    }

    /**
     * Support constructor for cloning the game
     *
     * @param p1    First Player instance
     * @param p2    Second Player instance
     * @param board Board instance
     */
    public OthelloGame(Player p1, Player p2, Board board) {
        this(p1, p2);
        this.board = board;
    }

    /**
     * Constructor for cloning the game
     *
     * @param othelloGame Existing OthelloGame instance
     */
    public OthelloGame(OthelloGame othelloGame) {
        this(new Player(othelloGame.players.get(0)),
                new Player(othelloGame.players.get(1)), othelloGame.board.deepCopy());
    }

    /**
     * Method that checks if the particular game is over.
     * A game can be over if one of the players has disconnected / left, the board is full,
     * or no more moves can be made by any of the players.
     *
     * @return true / false indicating whether the game is over
     */
    /*@pure; */
    @Override
    public boolean isGameOver() {
        return this.players.size() != 2 || this.board.isFull()
                || (this.gameTurnAllowedMoves.isEmpty()
                && this.board.getValidMoves(this.getPlayerTurn().mark().getOpposite()).isEmpty());
    }

    /**
     * Method that checks if a specific player in particular game is a winner. A player can be a winner,
     * if the game is over and the opponent has disconnected or the player has more marks on the field than the opponent.
     *
     * @param player Player implementation
     * @return true / false
     */
    /*@requires isGameOver();
      @requires isPlayerConnected(player);
      @ensures board.countMarks(player.mark()) > board.countMarks(player.mark().getOpposite()) ==> \result == true;
      @pure; */
    @Override
    public boolean isWinner(Player player) {
        return isGameOver() && isPlayerConnected(player) && (this.players.size() == 1
                || (this.board.countMarks(player.mark()) > this.board.countMarks(player.mark().getOpposite())));
    }

    /**
     * Method that attempts to retrieve the winner of the game, assuming the game is over
     *
     * @return null, if it's a draw, Player the winner otherwise
     */
    @Override
    public Player getWinner() {
        for (Player player : this.players) {
            if (this.isWinner(player)) {
                return player;
            }
        }

        return null;
    }

    /**
     * Method that checks if a specific player is connected to the particular game / participating
     *
     * @param player Player implementation
     * @return true / false
     */
    /*@ensures players.contains(players) ==> \result == true;
      @pure; */
    @Override
    public boolean isPlayerConnected(Player player) {
        return this.players.contains(player);
    }

    /**
     * Method that removes player from the list of players
     *
     * @param player Player instance
     */
    /*@requires player != null;
      @requires players.contains(players); */
    @Override
    public void removePlayer(Player player) {
        this.players.remove(player);
    }

    /**
     * Method that returns all connected players to the particular game
     *
     * @return List<Player>, list of players
     */
    /*@ensures (\forall int i; i >= 0 && i < players.size(); \result.get(i).equals(players.get(i)));
      @pure; */
    @Override
    public List<Player> getPlayers() {
        return this.players;
    }

    /**
     * Method that returns the Player of the current turn
     *
     * @return Player
     */
    /*@ensures players.contains(\result);
      @pure;*/
    @Override
    public Player getPlayerTurn() {
        return this.players.get(gameTurn);
    }

    /**
     * Method that checks if the provided move is valid.
     * A provided move is valid if its current players / bots turn,
     * the field is valid field on the board and opponents marks can be outflanked or the move is a passing move.
     *
     * @param move BoardMove
     * @return true / false
     */
    /*@requires move != null;
      @ensures move.getPlayer().equals(getPlayerTurn()) && move.isPassing() ==> \result == true;
      @ensures move.getPlayer().equals(getPlayerTurn())
        && board.isField(board.getIndex(move.getRow(), move.getColumn()))
            && gameTurnAllowedMoves.contains(move.getIndexCollection()) ==> \result == true;
      @pure; */
    @Override
    public boolean isValidMove(BoardMove move) {
        return move.getPlayer().equals(this.getPlayerTurn()) && (move.isPassing()
                || (Board.isField(Board.getIndex(move.getRow(), move.getColumn()))
                && this.gameTurnAllowedMoves.contains(move.getIndexCollection())));
    }

    /**
     * Method that attempts to convert index location on board to it's corresponding move object.
     * Assumes that the move is intended to be constructed for the player that has its turn in the game
     *
     * @param location int, location index on the board
     * @return null, if the conversion failed, otherwise BoardMove
     */
    /*@requires location >= 0 && location < 64; */
    public BoardMove locationToMove(int location) {
        // Check if the move is a passing move
        if (location == PASSING_MOVE_INDEX) return new BoardMove(this.getPlayerTurn());

        // Attempt to get the corresponding move index collection
        for (List<Integer> allowedMove : this.gameTurnAllowedMoves) {
            // Provided move is in the list of current turn allowed moves
            if (Board.getIndex(allowedMove.get(0), allowedMove.get(1)) == location) {
                // We pass the move validation forwards
                return new BoardMove(this.getPlayerTurn(), allowedMove);
            }
        }

        return null;
    }

    /**
     * Method that returns all valid moves that a player / bot could perform in this turn.
     *
     * @param player Player implementation
     * @return List<BoardMove>, list of valid moves
     */
    /*@requires players != null && players.contains(player);
      @requires !isGameOver(); */
    @Override
    public List<BoardMove> getValidMoves(Player player) {
        return this.board.getValidMoves(player.mark()).stream()
                .map(collection -> new BoardMove(player, collection)).toList();
    }

    /**
     * Method that performs a move, respecting that the proposed move is valid.
     * If the provided move is a passing move, nothing on board gets modified and the turn is given to the opponent
     *
     * @param move BoardMove
     */
    /*@requires move != null && isValidMove(move);
      @modifies board;
      @modifies gameTurn;
      @modifies gameTurnAllowedMoves; */
    @Override
    public void doMove(BoardMove move) {
        // Check if move is valid
        if (!isValidMove(move)) return;

        // Perform move if it's not passing and flip outflanked enemy marks
        if (!move.isPassing()) {
            this.board.flipFields(move.getRow(),
                    move.getColumn(),
                    move.getSupportRow(),
                    move.getSupportColumn(),
                    move.getExtensionRow(),
                    move.getExtensionColumn(),
                    move.getPlayer().mark());
        }

        // Updating game turn
        this.gameTurn = (this.gameTurn + 1) % this.players.size();

        // Updating valid moves
        this.gameTurnAllowedMoves = this.board.getValidMoves(this.getPlayerTurn().mark());
    }

    /**
     * Method that returns the board associated to the current game
     *
     * @return Board instance associated to the game
     */
    /*@pure; */
    @Override
    public Board getBoard() {
        return this.board;
    }

    /**
     * Method that returns the deep copy of current games state
     *
     * @return Deep copied BoardGame instance
     */
    @Override
    public BoardGame deepCopy() {
        return new OthelloGame(this);
    }
}
