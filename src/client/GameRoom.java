package client;

import client.handlers.GameHandler;

import java.io.IOException;
import java.io.PipedReader;
import java.io.PipedWriter;
import java.io.PrintWriter;

/**
 * "Helper" class that holds together the game handler of a particular game room.
 */
public class GameRoom {
    /**
     * Holds reference to the game handler that handles current ongoing client game.
     */
    private final GameHandler gameHandler;

    /**
     * Input for game handler that is going to be reading dispatched messages from the client UI.
     */
    private PipedReader pipedInput;

    /**
     * Output for client handler to write to.
     */
    private PrintWriter pipedOutput;

    /**
     * Returns the GameHandler instance associated to the GameRoom.
     *
     * @return GameHandler instance
     */
    protected GameHandler getGameHandler() {
        return this.gameHandler;
    }

    /**
     * Initializes the game room, game handler.
     */
    public GameRoom(Client client) {
        try {
            this.pipedInput = new PipedReader();
            this.pipedOutput = new PrintWriter(new PipedWriter(this.pipedInput), true);
        } catch (IOException ignored) { }

        this.gameHandler = new GameHandler(client, this.pipedInput);

        // Running the game handler
        new Thread(this.gameHandler).start();
    }

    /**
     * Method that forwards protocol message to the GameHandler instance.
     *
     * @param message String protocol message
     */
    public void forwardToGameHandler(String message) {
        this.pipedOutput.println(message);
    }
}
