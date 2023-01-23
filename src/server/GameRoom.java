package server;

import game.BoardGame;
import game.OthelloGame;
import game.board.BoardMark;
import game.players.HumanPlayer;

import java.io.IOException;
import java.io.PipedReader;
import java.io.PipedWriter;
import java.io.PrintWriter;

/**
 * "Helper" class that holds together the game handler of a particular game room
 */
public class GameRoom {
    /**
     * Holds reference back to the game handler of the particular room
     */
    private GameHandler gameHandler;

    /**
     * Holds the name of the room that is associated to the object
     */
    private String roomName;

    /**
     * Input for game handler that is going to be reading dispatched messages from the client handler
     */
    private PipedReader pipedInput;

    /**
     * Output for client handler to write to
     */
    private PrintWriter pipedOutput;

    /**
     * Initializes the game room, game handler
     */
    public GameRoom(Server server, String firstUsername, String secondUsername) {
        try {
            this.pipedInput = new PipedReader();
            this.pipedOutput = new PrintWriter(new PipedWriter(this.pipedInput), true);
        } catch (IOException e) {
            // TODO: Read how to properly handle
        }

        this.gameHandler = new GameHandler(server,
                new OthelloGame(
                        new HumanPlayer(firstUsername, BoardMark.BLACK),
                        new HumanPlayer(secondUsername, BoardMark.WHITE)),
                this.pipedInput);

        // Running the game handler
        new Thread(this.gameHandler).start();
    }

    /**
     * Getter for GameHandler instance
     * @return
     */
    public GameHandler getGameHandler() {
        return this.gameHandler;
    }

    /**
     * Method that forwards protocol message to the GameHandler instance
     * @param message
     */
    public void forwardToGameHandler(String message) {
        this.pipedOutput.println(message);
    }
}
