package game.board;

import game.OthelloGame;
import game.players.Player;

import java.util.Arrays;
import java.util.List;

/**
 * Class that represents a move object that gets applied on the board
 */
public class BoardMove {
    /**
     * Holds the player instance associated to the move
     */
    private final Player player;

    /**
     * Holds the board index collection pairs (row, column, support row, support column, extension row, extension column)
     */
    private final List<Integer> indexCollection;

    /**
     * Indicates whether the move is a passing move (player skips the turn)
     */
    private boolean isPassing = false;

    /**
     * Holds the default empty index collection that is assigned to passing moves
     */
    private static final List<Integer> PASSING_INDEX_COLLECTION = Arrays.asList(0, 0, 0, 0, 0, 0);

    /**
     * Constructor that initializes the move
     *
     * @param player Player instance
     * @param indexCollection List<Integer> collection of row, column, their outflanking pairs and extension point pair
     */
    public BoardMove(Player player, List<Integer> indexCollection) {
        this.player = player;
        this.indexCollection = indexCollection;
    }

    /**
     * Constructor that initializes the move stating the move is a passing move,
     * move should be passing if a player can't make any move in his turn or has decided to skip his turn.
     *
     * @param player Player instance
     */
    public BoardMove(Player player) {
        this(player, PASSING_INDEX_COLLECTION);
        this.isPassing = true;
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
    public List<Integer> getIndexCollection() {
        return this.indexCollection;
    }

    /**
     * Method that returns the particular moves endpoint row index
     * @return int row index, from 0 to 7
     */
    public int getRow() {
        return this.indexCollection.get(0);
    }

    /**
     * Method that returns the particular moves endpoint column index
     * @return int column index, from 0 to 7
     */
    public int getColumn() {
        return this.indexCollection.get(1);
    }

    /**
     * Method that returns the particular moves supporting (already placed mark) row index
     * @return int row index, from 0 to 7
     */
    public int getSupportRow() {
        return this.indexCollection.get(2);
    }

    /**
     * Method that returns the particular moves supporting (already placed mark) column index
     * @return int column index, from 0 to 7
     */
    public int getSupportColumn() {
        return this.indexCollection.get(3);
    }

    /**
     * Method that returns the particular moves singular extension in row direction
     * @return int row extension, from -1 to 1
     */
    public int getExtensionRow() {
        return this.indexCollection.get(4);
    }

    /**
     * Method that returns the particular moves singular extension in column direction
     * @return int column extension, from -1 to 1
     */
    public int getExtensionColumn() {
        return this.indexCollection.get(5);
    }

    /**
     * States whether a particular move is a passing move
     * @return true / false indicating whethere the move is a passing move
     */
    public boolean isPassing() {
        return this.isPassing;
    }

    /**
     * Method that returns the location on the board of the move
     * @return int, location on board, or 64 for passing move
     */
    public int getLocation() {
        return this.isPassing ? OthelloGame.PASSING_MOVE_INDEX : Board.getIndex(this.getRow(), this.getColumn());
    }
}
