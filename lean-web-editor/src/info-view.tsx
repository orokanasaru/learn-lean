import { InfoRecord, Message } from '@bryangingechen/lean-client-js-browser';
import React, { useEffect, useState } from 'react';
import { Position } from '.';
import { GoalWidget, GoalWidgetProps } from './goal-widget';
import { allMessages, server } from './langservice';
import { MessageWidget } from './message-widget';

enum DisplayMode {
  OnlyState, // only the state at the current cursor position including the tactic state
  AllMessage, // all messages
}

interface InfoViewProps {
  file: string;
  cursor?: Position;
}

export function InfoView(props: InfoViewProps) {
  const [goal, setGoal] = React.useState<GoalWidgetProps>();
  const [messages, setMessages] = React.useState<Message[]>([]);
  const [displayMode, setDisplayMode] = React.useState(DisplayMode.OnlyState);

  React.useEffect(() => {
    updateMessages();
    let timer = null; // debounce
    const subscription = server.allMessages.on(() => {
      if (timer) {
        clearTimeout(timer);
      }
      timer = setTimeout(() => {
        updateMessages();
        refreshGoal();
      }, 100);
    });

    return subscription.dispose;
  }, []);

  React.useEffect(() => {
    updateMessages();
    refreshGoal();
  }, [props.cursor]);

  function updateMessages() {
    setMessages(allMessages.filter((v) => v.file_name === props.file));
  }

  function refreshGoal() {
    if (!props.cursor) {
      return;
    }

    const position = props.cursor;
    server.info(props.file, position.line, position.column).then((res) => {
      setGoal(res.record && { goal: res.record, position });
    });
  }

  const displayGoal = displayMode === DisplayMode.OnlyState && goal && (
    <div key={'goal'}>
      <GoalWidget goal={goal.goal} position={goal.position} />
    </div>
  );

  const filteredMsgs =
    displayMode === DisplayMode.AllMessage
      ? messages
      : messages.filter(({ pos_col, pos_line, end_pos_col, end_pos_line }) => {
          if (!props.cursor) {
            return false;
          }
          const { line, column } = props.cursor;
          return (
            pos_line <= line &&
            ((!end_pos_line && line === pos_line) || line <= end_pos_line) &&
            (line !== pos_line || pos_col <= column) &&
            (line !== end_pos_line || end_pos_col >= column)
          );
        });

  const msgs = filteredMsgs.map((msg, i) => (
    <div key={i}>
      <MessageWidget msg={msg} />
    </div>
  ));

  return (
    <div style={{ overflow: 'auto', height: '100%' }}>
      <div className='infoview-buttons'>
        <img
          src='./display-goal-light.svg'
          title='Display Goal'
          style={{
            opacity: displayMode === DisplayMode.OnlyState ? 1 : 0.25,
          }}
          onClick={() => {
            setDisplayMode(DisplayMode.OnlyState);
          }}
        />
        <img
          src='./display-list-light.svg'
          title='Display Messages'
          style={{
            opacity: displayMode === DisplayMode.AllMessage ? 1 : 0.25,
          }}
          onClick={() => {
            setDisplayMode(DisplayMode.AllMessage);
          }}
        />
      </div>
      {displayGoal}
      {msgs}
    </div>
  );
}
