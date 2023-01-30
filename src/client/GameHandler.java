package client;

import client.exceptions.GameNotFoundException;
import client.exceptions.GameTurnViolationException;
import client.exceptions.InvalidMoveException;
import client.handlers.SysoutHandler;
import game.BoardGame;
import game.OthelloGame;
import game.board.AlgebraicNotationConversionFailed;
import game.board.Board;
import game.board.BoardMark;
import game.board.BoardMove;
import game.players.HumanPlayer;
import game.players.Player;
import networking.Protocol;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

/**
 * Runnable that handles assigned game state on the client
 */
public class GameHandler implements Runnable {
    /**
     * Holds the reference to the particular board game
     */
    private BoardGame game;

    /**
     * Holds the reference to the current initialized client
     */
    private final Client client;

    /**
     * Queue that holds the queue of approved move locations by the server that the client should keep track of
     */
    private final Queue<Integer> locationQueue = new LinkedList<>();

    /**
     * Input for game handler that is going to be reading dispatched messages from the client ui
     */
    private final Reader input;

    /**
     * Assigns the reference to the current initialized client
     *
     * @param client Client instance
     */
    public GameHandler(Client client, Reader input) {
        this.client = client;
        this.input = input;
    }

    /**
     * Method that returns the queue of un-applied server validated move locations
     *
     * @return Queue<Integer> of board move index locations
     */
    protected Queue<Integer> getQueue() {
        synchronized (this.locationQueue) {
            return this.locationQueue;
        }
    }

    /**
     * Internal method that adds move location to the queue if there is ongoing game
     * @param location int, move location
     */
    private void addToQueue(int location) {
        synchronized (this.locationQueue) {
            if (this.game == null) return;

            this.locationQueue.add(location);
            this.locationQueue.notify();
        }
    }

    /**
     * Indicates whether the GameHandler has an ongoing game already assigned to it
     *
     * @return boolean
     */
    protected boolean hasOngoingGame() {
        return this.game != null;
    }

    /**
     * Method that returns the client instance associated to the GameHandler
     * @return Client instance
     */
    protected Client getClient() {
        return this.client;
    }

    /**
     * Method that returns the ongoing game instance associated to the GameHandler
     * @return BoardGame instance
     */
    protected BoardGame getGame() {
        return this.game;
    }

    /**
     * Method that sends appropriate protocol message indicating that the turn is to be skipped
     * @throws GameNotFoundException if there is no ongoing game at the moment that the method is called
     */
    protected void skipTurn() throws GameNotFoundException {
        // Check if there is ongoing game
        if (this.game == null) {
            throw new GameNotFoundException();
        }

        this.client.attemptMove(OthelloGame.PASSING_MOVE_INDEX);
    }

    /**
     * Method that outputs SAN formatted move hints to the client
     * @throws GameNotFoundException if there is no ongoing game at the moment that the method is called
     * @throws GameTurnViolationException if the method is called at the moment when its opponents game turn
     */
    protected void giveHint() throws GameNotFoundException, GameTurnViolationException {
        // Check if there is ongoing game
        if (this.game == null) {
            throw new GameNotFoundException();
        }

        // Check if it's current clients turn
        if (!this.game.getPlayerTurn().getUsername().equals(this.client.getUsername())) {
            throw new GameTurnViolationException();
        }

        StringBuilder hintResult = new StringBuilder(SysoutHandler.IDEA + " Available moves ");

        this.game.getValidMoves(this.game.getPlayerTurn())
                .forEach(boardMove -> {
                    String converted = Board.convertToSAN(boardMove.getRow(), boardMove.getColumn());

                    if (hintResult.indexOf(converted) == -1) {
                        hintResult.append(converted).append(" ");
                    }
                });

        this.client.getMessageHandler().incomingMessage(hintResult.toString());
    }

    /**
     * Method that handles client typed moves by converting them, validating on client side
     * and forwarding to the server
     *
     * @param desiredMoveSAN String, if null is passed then move is interpreted as a skipping move,
     *                       otherwise SAN move
     * @throws GameNotFoundException if there is no ongoing game at the moment that the method is called
     * @throws GameTurnViolationException if the method is called at the moment when its opponents game turn
     * @throws InvalidMoveException if the provided move is not valid
     * @throws AlgebraicNotationConversionFailed if provided move in SAN couldn't be converted to a valid location on board
     */
    protected void handleMove(String desiredMoveSAN) throws GameNotFoundException, GameTurnViolationException,
            InvalidMoveException, AlgebraicNotationConversionFailed {
        // Check if there is ongoing game
        if (this.game == null) {
            throw new GameNotFoundException();
        }

        // Check if it's current clients turn
        if (!this.game.getPlayerTurn().getUsername().equals(this.client.getUsername())) {
            throw new GameTurnViolationException();
        }

        try {
            // Check if user has passed a skipping move
            if (desiredMoveSAN == null) {
                this.skipTurn();
                return;
            }

            // Attempting to convert the location
            int convertedLocation = Board.convertFromSAN(desiredMoveSAN);

            // Location was successfully converted, need to validate if it's even valid move in current games state
            BoardMove desiredMove = this.game.locationToMove(convertedLocation);

            if (desiredMove == null || !this.game.isValidMove(desiredMove)) {
                throw new InvalidMoveException(desiredMove);
            }

            // Otherwise move is valid, we send it over to the server
            this.client.attemptMove(convertedLocation);

        } catch (AlgebraicNotationConversionFailed e) {
            // Conversion failed, re-throwing the exception
            throw new AlgebraicNotationConversionFailed(desiredMoveSAN);
        }
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        try (BufferedReader bf = new BufferedReader(this.input)) {
            // Reading line by line
            String line;

            while ((line = bf.readLine()) != null) {
                String command = Protocol.commandExtract(line);

                // Fall-through is not needed, using enhanced switch statement
                switch (command) {
                    case Protocol.NEWGAME -> {
                        // We received an event from the client, that a new game has started
                        // We initialize the game
                        List<String> usernames = Protocol.newGameExtract(line);
                        Player firstPlayer = new HumanPlayer(usernames.get(0), BoardMark.BLACK);
                        Player secondPlayer = new HumanPlayer(usernames.get(1), BoardMark.WHITE);

                        this.game = new OthelloGame(firstPlayer, secondPlayer);

                        // Forwarding 'notifications' to the client
                        this.client.getMessageHandler().incomingMessage(SysoutHandler.GAME + " A new match found!")
                                .incomingMessage(String.format("%s Player '%s' %s against Player '%s' %s",
                                    SysoutHandler.INFO, firstPlayer.getUsername(), firstPlayer.getMark(),
                                    secondPlayer.getUsername(), secondPlayer.getMark()))
                                .incomingMessage(String.format("%s Player '%s' starts",
                                    SysoutHandler.INFO, firstPlayer.getUsername()))
                                .incomingMessage(this.game.getBoard().toString());

                        // Clearing the location queue
                        this.locationQueue.clear();

                        // Spawning a LocationHandler that will be responsible for applying the positions on the board
                        new Thread(new LocationHandler(this)).start();
                    }
                    case Protocol.GAMEOVER -> {
                        // There must be an ongoing game for it to end
                        if (this.game == null) break;

                        // Extracting the game over reason
                        String reason = Protocol.gameOverExtractReason(line);
                        StringBuilder descriptive = new StringBuilder(SysoutHandler.FINISH + " Game over, ");

                        if (reason.equals(Protocol.DISCONNECT)) {
                            descriptive.append("opponent has disconnected, you are the winner!");
                        } else if (reason.equals(Protocol.DRAW)) {
                            descriptive.append("it's a draw!");
                        } else {
                            // Otherwise it's VICTORY, someone won, if winner is not provided by the server,
                            // we must get it ourselves
                            Player winnerPlayer = this.game.getWinner();
                            String winner = Protocol.gameOverExtractWinner(line).orElse(winnerPlayer.getUsername());
                            descriptive.append(winner).append(" has won, ").append(winnerPlayer.getUsername()
                                    .equals(this.client.getUsername()) ? "you won!" : "you lost!");
                        }

                        this.client.getMessageHandler().incomingMessage(descriptive.toString());
                        this.game = null;
                    }
                    // Extracting the move that was validated by the server and passed to use by the client,
                    // adding the move to the queue for the LocationHandler to handle
                    case Protocol.MOVE -> this.addToQueue(Protocol.moveExtract(line));
                }
            }
        } catch (IOException e) {
            // TODO: Read how to properly handle this
        }
    }
}
