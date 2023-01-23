package game.board;

import game.players.Player;

import java.util.List;

public class BoardMove {
    private Player player;
    private List<Integer> indexCollection;

    /**
     * Constructor that initializes the object
     * @param player Player implementation
     * @param indexCollection List<Integer> collection of row, column, their outflanking pairs and extension point pair
     */
    public BoardMove(Player player, List<Integer> indexCollection) {
        this.player = player;
        this.indexCollection = indexCollection;
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
     * Method that returns the particular moves mark type
     * @return BoardMark
     */
    /*@pure; @*/
    public BoardMark getMark() {
        return this.player.getMark();
    }

    public int getRow() {
        return this.indexCollection.get(0);
    }

    public int getColumn() {
        return this.indexCollection.get(1);
    }

    public int getSupportRow() {
        return this.indexCollection.get(2);
    }

    public int getSupportColumn() {
        return this.indexCollection.get(3);
    }

    public int getExtensionRow() {
        return this.indexCollection.get(4);
    }

    public int getExtensionColumn() {
        return this.indexCollection.get(5);
    }
}
