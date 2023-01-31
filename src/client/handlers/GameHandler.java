package client.handlers;

import client.Client;
import client.exceptions.AIAssignedException;
import client.exceptions.GameNotFoundException;
import client.exceptions.GameTurnViolationException;
import client.exceptions.InvalidMoveException;
import client.operators.SysoutOperator;
import game.BoardGame;
import game.OthelloGame;
import game.ai.ComputerPlayer;
import game.ai.ComputerPlayerFactory;
import game.board.exceptions.AlgebraicNotationConversionFailed;
import game.board.Board;
import game.board.BoardMark;
import game.board.BoardMove;
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
     * Holds the reference to the AI assigned to the current game
     */
    private ComputerPlayer computerPlayer;

    /**
     * Holds whether the computer player can determine move
     */
    private boolean computerPlayerTurn = false;

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
     * Method that states if at any given moment at the game, the AI is playing for the current client
     * @return true / false
     */
    protected boolean isComputerPlaying() {
        return this.computerPlayer != null;
    }

    /**
     * Method that returns the ComputerPlayer instance attached to the current game
     * @return null, if there is no AI assigned at the moment, ComputerPlayer otherwise
     */
    protected ComputerPlayer getComputerPlayer() {
        return this.computerPlayer;
    }

    /**
     * Method that states whether it's clients turn to go in the game
     * @return true / false
     */
    protected boolean isClientsTurn() {
        return this.game.getPlayerTurn().username().equals(this.client.getUsername());
    }

    /**
     * Method that indicates whether the ComputerPlayer can perform a move
     * @return true / false
     */
    protected boolean isComputerPlayerTurn() {
        return this.computerPlayerTurn;
    }

    /**
     * Method that updates the state status that indicates if ComputerPlayer can perform a move
     * @param state boolean updated state
     */
    protected void setComputerPlayerTurn(boolean state) {
        this.computerPlayerTurn = state;
    }

    /**
     * Method that sends appropriate protocol message indicating that the turn is to be skipped
     * @throws GameNotFoundException if there is no ongoing game at the moment that the method is called
     */
    public void skipTurn() throws GameNotFoundException {
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
    public void giveHint() throws GameNotFoundException, GameTurnViolationException {
        // Check if there is ongoing game
        if (this.game == null) {
            throw new GameNotFoundException();
        }

        // Check if it's current clients turn
        if (!this.isClientsTurn()) {
            throw new GameTurnViolationException();
        }

        StringBuilder hintResult = new StringBuilder(SysoutOperator.IDEA + " Available moves ");

        this.game.getValidMoves(this.game.getPlayerTurn())
                .forEach(boardMove -> {
                    String converted = Board.convertToSAN(boardMove.getRow(), boardMove.getColumn());

                    if (hintResult.indexOf(converted) == -1) {
                        hintResult.append(converted).append(" ");
                    }
                });

        this.client.getMessageOperator().incomingMessage(hintResult.toString());
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
     * @throws AIAssignedException if AI is assigned and determining moves for the client
     */
    public void handleMove(String desiredMoveSAN) throws GameNotFoundException, GameTurnViolationException,
            InvalidMoveException, AlgebraicNotationConversionFailed, AIAssignedException {
        // Check if there is ongoing game
        if (this.game == null) {
            throw new GameNotFoundException();
        }

        // Check if it's current clients turn
        if (!this.isClientsTurn()) {
            throw new GameTurnViolationException();
        }

        // Check if AI is supposed to determine the move
        if (this.isComputerPlaying()) {
            throw new AIAssignedException();
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
     * Method that assigns an AI to the ongoing game
     * @param level int, level of the ai. From 1 to 2
     * @throws GameNotFoundException if there is no ongoing game at the moment that the method is called
     * @throws AIAssignedException if an AI is already assigned to the current game
     */
    public void assignAI(int level) throws GameNotFoundException, AIAssignedException {
        // Check if there is ongoing game
        if (this.game == null) {
            throw new GameNotFoundException();
        }

        // Check if an AI is already assigned to the current game
        if (this.computerPlayer != null) {
            throw new AIAssignedException();
        }

        // Otherwise assign an AI to play for the client
        this.computerPlayer = new ComputerPlayerFactory().generateComputerPlayer(level);

        // Spawning a AIHandler that will be responsible for playing for the client
        new Thread(new AIHandler(this)).start();

        // Update the state
        this.setComputerPlayerTurn(this.isClientsTurn());
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
                    case Protocol.NEWGAME -> handleNewGame(line);
                    case Protocol.GAMEOVER -> handleGameOver(line);
                    // Extracting the move that was validated by the server and passed to use by the client,
                    // adding the move to the queue for the LocationHandler to handle
                    case Protocol.MOVE -> this.addToQueue(Protocol.moveExtract(line));
                }
            }
        } catch (IOException ignored) {}
    }

    /**
     * Internal method that handles the new game protocol message
     * @param line String protocol line
     */
    private void handleNewGame(String line) {
        // We received an event from the client, that a new game has started
        // We initialize the game
        List<String> usernames = Protocol.newGameExtract(line);
        Player firstPlayer = new Player(usernames.get(0), BoardMark.BLACK);
        Player secondPlayer = new Player(usernames.get(1), BoardMark.WHITE);

        this.game = new OthelloGame(firstPlayer, secondPlayer);

        // Forwarding 'notifications' to the client
        this.client.getMessageOperator().incomingMessage(SysoutOperator.GAME + " A new match found!")
                .incomingMessage(String.format("%s Player '%s' %s against Player '%s' %s",
                        SysoutOperator.INFO, firstPlayer.username(), firstPlayer.mark(),
                        secondPlayer.username(), secondPlayer.mark()))
                .incomingMessage(String.format("%s Player '%s' starts",
                        SysoutOperator.INFO, firstPlayer.username()))
                .incomingMessage(this.game.getBoard().toString());

        // Clearing the location queue
        this.locationQueue.clear();

        // Spawning a LocationHandler that will be responsible for applying the positions on the board
        new Thread(new LocationHandler(this)).start();
    }

    /**
     * Internal helper method that formats game over reason
     * @param line String protocol line
     * @return String formatted, or null if reason wasn't determined
     */
    private String gameOverFormat(String line) {
        String reason = Protocol.gameOverExtractReason(line);

        // Invalid reason
        if (reason == null) return null;

        StringBuilder descriptive = new StringBuilder(SysoutOperator.FINISH + " Game over, ");

        if (reason.equals(Protocol.DISCONNECT)) {
            descriptive.append("opponent has disconnected, you are the winner!");
        } else if (reason.equals(Protocol.DRAW)) {
            descriptive.append("it's a draw!");
        } else {
            // Otherwise it's VICTORY, someone won, if winner is not provided by the server,
            // we must get it ourselves
            Player winnerPlayer = this.game.getWinner();
            String winner = Protocol.gameOverExtractWinner(line).orElse(winnerPlayer.username());
            descriptive.append(winner).append(" has won, ").append(winnerPlayer.username()
                    .equals(this.client.getUsername()) ? "you won!" : "you lost!");
        }

        return descriptive.toString();
    }

    /**
     * Internal method that handles the game over protocol message
     * @param line String protocol line
     */
    private void handleGameOver(String line) {
        // There must be an ongoing game for it to end
        if (this.game == null) return;

        // Extracting the game over formatted reason
        String reasonFormatted = this.gameOverFormat(line);

        // Invalid reason
        if (reasonFormatted == null) return;

        // Informing the client
        this.client.getMessageOperator().incomingMessage(reasonFormatted);

        // Updating state
        this.game = null;
        this.computerPlayer = null;
    }
}
